// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

pub mod translate_address;
pub mod translate_attribute;
pub mod translate_constant;
pub mod translate_exp;
pub mod translate_friend;
pub mod translate_function;
pub mod translate_let;
pub mod translate_modifiers;
pub mod translate_module;
pub mod translate_script;
pub mod translate_spec;
pub mod translate_struct;
pub mod translate_type;
pub mod translate_use;

use std::mem;

use move_command_line_common::address::NumericalAddress;
use move_ir_types::location::{Loc, Spanned};
use move_symbol_pool::Symbol;

use crate::{
    attr_derivation, diag,
    diagnostics::{codes::Severity, Diagnostic, Diagnostics},
    parser::{comments::Comment, lexer::Tok},
    shared::{CompilationEnv, Name, NamedAddressMaps},
    CommentMap, MatchedFileCommentMap,
};

use super::{super::ast as T, ast as P};

pub struct Context<'env> {
    matched_doc_comments: MatchedFileCommentMap,
    env: &'env mut CompilationEnv,
}

impl<'env> Context<'env> {
    pub fn insert_comments(&mut self, loc: u32, comments: Vec<Comment>) {
        let comment_content = comments
            .iter()
            .map(|c| c.content.as_str())
            .collect::<Vec<_>>()
            .join("\n");
        self.matched_doc_comments.insert(loc, comment_content);
    }

    pub fn new(env: &'env mut CompilationEnv) -> Self {
        Self {
            matched_doc_comments: Default::default(),
            env,
        }
    }

    pub fn take_comments_map(&mut self) -> MatchedFileCommentMap {
        mem::take(&mut self.matched_doc_comments)
    }
}

pub fn translate_program(
    compilation_env: &mut CompilationEnv,
    named_address_maps: NamedAddressMaps,
    parsed_tree: P::Program,
) -> Result<(T::Program, CommentMap), Diagnostics> {
    let mut context = Context::new(compilation_env);
    // let (pprog, comments, mut diags) = translate_program_(&mut context, parsed_tree)?;

    let res = translate_program_(named_address_maps, &mut context, parsed_tree);

    let additional_diags =
        match compilation_env.check_diags_at_or_above_severity(Severity::BlockingError) {
            Ok(_) => Diagnostics::new(),
            Err(diags) => diags,
        };

    match res {
        Ok((pprog, comments)) => Ok((pprog, comments)),
        Err(mut errs) => {
            errs.extend(additional_diags);
            Err(errs)
        }
    }
}

fn translate_program_(
    named_address_maps: NamedAddressMaps,
    context: &mut Context,
    ast: P::Program,
) -> Result<(T::Program, CommentMap), Diagnostics> {
    let mut source_comments = CommentMap::new();
    let mut source_defs = vec![];
    let mut diags = Diagnostics::new();
    for def in ast.source_definitions.iter() {
        match translate_def(context, def) {
            Ok(res) => source_defs.extend(res),
            Err(diag) => diags.add(diag),
        };

        let comments = context.take_comments_map();
        source_comments.insert(def.file_hash, comments);
    }

    let mut lib_def = vec![];
    for def in ast.lib_definitions.iter() {
        match translate_def(context, def) {
            Ok(res) => lib_def.extend(res),
            Err(diag) => diags.add(diag),
        };

        let comments = context.take_comments_map();
        source_comments.insert(def.file_hash, comments);
    }

    // Run attribute expansion on all source definitions, passing in the matching named address map.
    for T::PackageDefinition {
        named_address_map: idx,
        def,
        ..
    } in source_defs.iter_mut()
    {
        attr_derivation::derive_from_attributes(context.env, named_address_maps.get(*idx), def);
    }

    if diags.is_empty() {
        Ok((
            T::Program {
                named_address_maps,
                source_definitions: source_defs,
                lib_definitions: lib_def,
            },
            source_comments,
        ))
    } else {
        Err(diags)
    }
}

fn translate_def(
    context: &mut Context,
    ast: &P::PackageDefinition,
) -> Result<Vec<T::PackageDefinition>, Diagnostic> {
    let defs = ast
        .source_trees
        .iter()
        .map(|branch| match branch {
            P::Definition::Module(module) => {
                let res = translate_module::translate_module(context, &ast, &module)?;

                Ok(T::PackageDefinition {
                    package: ast.package,
                    named_address_map: ast.named_address_map,
                    def: T::Definition::Module(res),
                })
            }
            P::Definition::Address(address) => {
                let res = translate_address::translate_address(context, &ast, &address)?;
                Ok(T::PackageDefinition {
                    package: ast.package,
                    named_address_map: ast.named_address_map,
                    def: T::Definition::Address(res),
                })
            }
            P::Definition::Script(script) => {
                let res = translate_script::translate_script(context, &ast, &script)?;
                Ok(T::PackageDefinition {
                    package: ast.package,
                    named_address_map: ast.named_address_map,
                    def: T::Definition::Script(res),
                })
            }
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(defs)
}

pub fn spanned<T>(loc: Loc, value: T) -> Spanned<T> {
    Spanned { loc, value }
}

pub fn spanned_between(first: &P::ParsedToken, second: &P::ParsedToken) -> Loc {
    Loc::new(
        first.value.loc.file_hash(),
        first.value.loc.start(),
        second.value.loc.end(),
    )
}

pub fn translate_token_to_name(
    ast: &P::PackageDefinition,
    token: &P::ParsedToken,
) -> Result<Name, Diagnostic> {
    let loc = token.token_range.loc(&ast.source_tokens);

    if token.value.kind != Tok::Identifier {
        return Err(unexpected_token_error(loc, "an identifier", ""));
    }
    let symbol = token.value.content;
    Ok(spanned(loc, symbol))
}

pub fn translate_token_to_leading_name_access(
    ast: &P::PackageDefinition,
    token: &P::ParsedToken,
) -> Result<T::LeadingNameAccess, Diagnostic> {
    let loc = token.token_range.loc(&ast.source_tokens);
    match token.value.kind {
        Tok::Identifier => {
            let n = translate_token_to_name(ast, token)?;
            Ok(spanned(loc, T::LeadingNameAccess_::Name(n)))
        }
        Tok::NumValue => {
            let sp!(loc, addr) = translate_token_to_address_byte(ast, token)?;
            Ok(spanned(loc, T::LeadingNameAccess_::AnonymousAddress(addr)))
        }
        _ => Err(unexpected_token_error(
            loc,
            "an address or an identifier",
            "",
        )),
    }
}

fn translate_token_to_address_byte(
    ast: &P::PackageDefinition,
    token: &P::ParsedToken,
) -> Result<Spanned<NumericalAddress>, Diagnostic> {
    let loc = token.token_range.loc(&ast.source_tokens);
    let addr_res = NumericalAddress::parse_str(&token.value.content);
    match addr_res {
        Ok(addr_) => Ok(spanned(loc, addr_)),
        Err(msg) => Err(diag!(Syntax::InvalidAddress, (loc, msg))),
    }
}

pub fn translate_value(
    ast: &P::PackageDefinition,
    token: &P::Value,
) -> Result<T::Value, Diagnostic> {
    let loc = token.token_range.loc(&ast.source_tokens);

    let value = match token.value() {
        P::Value_::Address(t) => {
            T::Value_::Address(translate_token_to_leading_name_access(ast, &t)?)
        }
        P::Value_::Literal(t) => match t.kind {
            Tok::True => T::Value_::Bool(true),
            Tok::False => T::Value_::Bool(false),
            Tok::NumValue => {
                let num = t.content;
                T::Value_::Num(num)
            }
            Tok::NumTypedValue => {
                let num = t.content;
                T::Value_::Num(num)
            }

            Tok::ByteStringValue => parse_byte_string(&t.content)?,
            _ => {
                return Err(unexpected_token_error(
                    loc,
                    "parse_value called with invalid token",
                    "",
                ))
            }
        },
    };
    Ok(spanned(loc, value))
}

pub fn unexpected_token_error(loc: Loc, unexpected: &str, expected: &str) -> Diagnostic {
    diag!(
        Syntax::UnexpectedToken,
        (loc, format!("Unexpected {}", unexpected)),
        (loc, format!("Expected {}", expected)),
    )
}

// Parse a byte string:
//      ByteString = <ByteStringValue>
fn parse_byte_string(s: &str) -> Result<T::Value_, Diagnostic> {
    let text = Symbol::from(&s[2..s.len() - 1]);
    let value_ = if s.starts_with("x\"") {
        T::Value_::HexString(text)
    } else {
        assert!(s.starts_with("b\""));
        T::Value_::ByteString(text)
    };
    Ok(value_)
}

pub fn translate_name_access_chain(
    ast: &P::PackageDefinition,
    names: &P::NameAccessChain,
) -> Result<T::NameAccessChain, Diagnostic> {
    let loc = names.token_range.loc(&ast.source_tokens);
    match &names.value[..] {
        [fir] => Ok(spanned(
            loc,
            T::NameAccessChain_::One(translate_token_to_name(ast, fir)?),
        )),
        [fir, sec] => {
            let leading = translate_token_to_leading_name_access(ast, fir)?;
            let name = translate_token_to_name(ast, sec)?;
            Ok(spanned(loc, T::NameAccessChain_::Two(leading, name)))
        }
        [fir, sec, third] => {
            let leading = translate_token_to_leading_name_access(ast, fir)?;
            let sec_name = translate_token_to_name(ast, sec)?;
            let third_name = translate_token_to_name(ast, third)?;
            let span_fir_sec = spanned_between(fir, sec);
            Ok(spanned(
                loc,
                T::NameAccessChain_::Three(spanned(span_fir_sec, (leading, sec_name)), third_name),
            ))
        }
        _ => Err(diag!(
            Declarations::InvalidAddress,
            (
                loc,
                "The amount of names of access chain could not exceed 3."
            )
        )),
    }
}

pub fn translate_ability(
    ast: &P::PackageDefinition,
    token: &P::Name,
) -> Result<T::Ability, Diagnostic> {
    let loc = token.loc(&ast.source_tokens);
    let value = match token.value().kind {
        Tok::Copy => T::Ability_::Copy,
        Tok::Identifier if token.value().content.as_str() == T::Ability_::DROP => T::Ability_::Drop,
        Tok::Identifier if token.value().content.as_str() == T::Ability_::STORE => {
            T::Ability_::Store
        }
        Tok::Identifier if token.value().content.as_str() == T::Ability_::KEY => T::Ability_::Key,
        _ => {
            let msg = format!(
                "Unexpected {}. Expected a type ability, one of: 'copy', 'drop', 'store', or 'key'",
                token.value().content
            );
            return Err(diag!(Syntax::UnexpectedToken, (loc, msg),));
        }
    };
    Ok(spanned(loc, value))
}

fn translate_field(ast: &P::PackageDefinition, field: &P::Field) -> Result<T::Field, Diagnostic> {
    Ok(T::Field(translate_token_to_name(ast, &field)?))
}

pub fn translate_var(ast: &P::PackageDefinition, token: &P::Name) -> Result<T::Var, Diagnostic> {
    let name = translate_token_to_name(ast, token)?;
    Ok(T::Var(name))
}
