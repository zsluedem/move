// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

pub mod parse_address_block;
pub mod parse_attributes;
pub mod parse_exp;
pub mod parse_friend;
pub mod parse_function;
pub mod parse_identifier;
pub mod parse_modifiers;
pub mod parse_module;
pub mod parse_script;
pub mod parse_spec;
pub mod parse_struct;
pub mod parse_type;
pub mod parse_use;

use std::{fs::File, io::Read};

use move_command_line_common::files::FileHash;
use move_symbol_pool::Symbol;

use crate::{
    diag,
    diagnostics::{Diagnostic, Diagnostics, FilesSourceText},
    parser::{ast::ENTRY_MODIFIER, comments::verify_string, lexer::Tok, syntax::make_loc},
};

use self::{
    parse_address_block::parse_address_block, parse_attributes::parse_attributes_vec,
    parse_exp::parse_sequence_item, parse_function::parse_function,
    parse_modifiers::parse_module_member_modifiers, parse_module::parse_module,
    parse_script::parse_script, parse_struct::parse_struct,
};

use super::{
    ast::{
        Attributes, Definition, Field, LeadingNameAccess, NameAccessChain, ParsedToken, ParsedTree,
        SequenceItem, Value, Value_, Var,
    },
    lexer::{FidelityLexer, Token},
};

pub struct Context<'input> {
    tokens: &'input mut FidelityLexer<'input>,
}

impl<'input> Context<'input> {
    fn new(tokens: &'input mut FidelityLexer<'input>) -> Self {
        Self { tokens }
    }
}

// Parse a file:
//      File =
//          (<Attributes> (<AddressBlock> | <Module> | <Script>))*
pub fn parse_definition(context: &mut Context) -> Result<Vec<Definition>, Diagnostic> {
    let mut defs = vec![];
    // Advance Begin of file
    context.tokens.advance()?;
    while context.tokens.peek() != Tok::EOF {
        let attributes = parse_attributes_vec(context)?;
        defs.push(match context.tokens.peek() {
            Tok::Spec | Tok::Module => parse_module(context, attributes)?,
            Tok::Script => parse_script(context, attributes)?,
            Tok::Identifier if context.tokens.content() == "address" => {
                parse_address_block(context, attributes)?
            }
            _ => {
                return Err(context
                    .tokens
                    .unexpected_token_error("address, spec, module or script"))
            }
        })
    }
    Ok(defs)
}

pub fn parse_tree(context: &mut Context) -> Result<ParsedTree, Diagnostic> {
    let tok = context.tokens.peek();
    let attrs = parse_attributes_vec(context)?;
    match tok {
        Tok::Fun => parse_function(vec![], context, attrs),
        Tok::Struct => parse_struct(vec![], context, attrs),
        Tok::Public | Tok::Native => parse_modifier_follow(context, attrs),
        Tok::Identifier if context.tokens.content() == ENTRY_MODIFIER => {
            parse_modifier_follow(context, attrs)
        }
        _ => parse_sequence(context, attrs),
    }
}

fn parse_modifier_follow(
    context: &mut Context,
    attributes: Vec<Attributes>,
) -> Result<ParsedTree, Diagnostic> {
    let modifiers = parse_module_member_modifiers(context)?;
    match context.tokens.peek() {
        Tok::Fun => parse_function(modifiers, context, attributes),
        Tok::Struct => parse_struct(modifiers, context, attributes),
        _ => Err(context.tokens.unexpected_token_error("a fun or a struct")),
    }
}

fn parse_sequence(
    context: &mut Context,
    attributes: Vec<Attributes>,
) -> Result<ParsedTree, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    let item = parse_sequence_item(context, attributes)?;
    let end_loc = context.tokens.tokens_loc();
    let token_range = context.tokens.token_range(start_loc, end_loc);
    Ok(ParsedTree::Sequence(SequenceItem::new(item, token_range)))
}

// Parse an identifier:
//      Identifier = <IdentifierValue>
pub fn parse_identifier(context: &mut Context) -> Result<ParsedToken, Diagnostic> {
    if context.tokens.peek() != Tok::Identifier {
        return Err(context.tokens.unexpected_token_error("an identifier"));
    }
    let token = context.tokens.advance()?;
    Ok(token)
}

// Parse the beginning of an access, either an address or an identifier:
//      LeadingNameAccess = <NumericalAddress> | <Identifier>
pub fn parse_leading_name_access(context: &mut Context) -> Result<LeadingNameAccess, Diagnostic> {
    parse_leading_name_access_(context, || "an address or an identifier")
}

// Parse the beginning of an access, either an address or an identifier with a specific description
pub fn parse_leading_name_access_<'a, F: FnOnce() -> &'a str>(
    context: &mut Context,
    item_description: F,
) -> Result<LeadingNameAccess, Diagnostic> {
    match context.tokens.peek() {
        Tok::Identifier | Tok::NumValue => {
            let addr = context.tokens.advance()?;
            Ok(addr)
        }
        _ => Err(context.tokens.unexpected_token_error(item_description())),
    }
}

// Parse a value:
//      Value =
//          "@" <LeadingAccessName>
//          | "true"
//          | "false"
//          | <Number>
//          | <NumberTyped>
//          | <ByteString>
pub fn maybe_parse_value(context: &mut Context) -> Result<Option<Value>, Diagnostic> {
    match context.tokens.peek() {
        Tok::AtSign => {
            let start_token_index = context.tokens.tokens_loc();
            context.tokens.advance()?;
            let addr = parse_leading_name_access(context)?;
            let end_token_index = context.tokens.tokens_loc();
            Ok(Some(Value::new(
                Value_::Address(addr),
                context
                    .tokens
                    .token_range(start_token_index, end_token_index),
            )))
        }
        Tok::True | Tok::False | Tok::NumTypedValue | Tok::ByteStringValue => {
            let lit = context.tokens.advance()?;
            Ok(Some(Value::new(
                Value_::Literal(lit.value),
                lit.token_range,
            )))
        }
        Tok::NumValue => {
            //  If the number is followed by "::", parse it as the beginning of an address access
            if let Ok(Tok::ColonColon) = context.tokens.lookahead() {
                return Ok(None);
            }
            let lit = context.tokens.advance()?;
            Ok(Some(Value::new(
                Value_::Literal(lit.value),
                lit.token_range,
            )))
        }
        _ => Ok(None),
    }
}
pub fn parse_value(context: &mut Context) -> Result<Value, Diagnostic> {
    Ok(maybe_parse_value(context)?.expect("parse_value called with invalid token"))
}

// Parse a module access (a variable, struct type, or function):
//      NameAccessChain = <LeadingNameAccess> ( "::" <Identifier> ( "::" <Identifier> )? )?
pub fn parse_name_access_chain<'a, F: FnOnce() -> &'a str>(
    context: &mut Context,
    item_description: F,
) -> Result<NameAccessChain, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    let ln = parse_leading_name_access_(context, item_description)?;
    let mut names = vec![ln];
    while context.tokens.peek() == Tok::ColonColon {
        context.tokens.consume_token(Tok::ColonColon)?;
        let name = parse_identifier(context)?;
        names.push(name)
    }
    let end_loc = context.tokens.tokens_loc();
    Ok(NameAccessChain::new(
        names,
        context.tokens.token_range(start_loc, end_loc),
    ))
}
pub fn parse_comma_list<F, R>(
    context: &mut Context,
    start_token: Tok,
    end_token: Tok,
    parse_list_item: F,
    item_description: &str,
) -> Result<Vec<R>, Diagnostic>
where
    F: Fn(&mut Context) -> Result<R, Diagnostic>,
{
    let start_loc = context.tokens.start_loc();
    context.tokens.consume_token(start_token)?;
    parse_comma_list_after_start(
        context,
        start_loc,
        start_token,
        end_token,
        parse_list_item,
        item_description,
    )
}

// Parse a comma-separated list of items, including the specified ending token, but
// assuming that the starting token has already been consumed.
pub fn parse_comma_list_after_start<F, R>(
    context: &mut Context,
    start_loc: usize,
    start_token: Tok,
    end_token: Tok,
    parse_list_item: F,
    item_description: &str,
) -> Result<Vec<R>, Diagnostic>
where
    F: Fn(&mut Context) -> Result<R, Diagnostic>,
{
    context.tokens.adjust_token(end_token);
    if context.tokens.match_token(end_token)? {
        return Ok(vec![]);
    }
    let mut v = vec![];
    loop {
        if context.tokens.peek() == Tok::Comma {
            let loc = context.tokens.current_loc();
            return Err(diag!(
                Syntax::UnexpectedToken,
                (loc, format!("Expected {}", item_description))
            ));
        }
        v.push(parse_list_item(context)?);
        context.tokens.adjust_token(end_token);
        if context.tokens.match_token(end_token)? {
            break Ok(v);
        }
        if !context.tokens.match_token(Tok::Comma)? {
            let loc = context.tokens.current_loc();
            let loc2 = make_loc(context.tokens.file_hash(), start_loc, start_loc);
            return Err(diag!(
                Syntax::UnexpectedToken,
                (loc, format!("Expected '{}'", end_token)),
                (loc2, format!("To match this '{}'", start_token)),
            ));
        }
        context.tokens.adjust_token(end_token);
        if context.tokens.match_token(end_token)? {
            break Ok(v);
        }
    }
}

// Parse a list of items, without specified start and end tokens, and the separator determined by
// the passed function `parse_list_continue`.
fn parse_list<C, F, R>(
    context: &mut Context,
    mut parse_list_continue: C,
    parse_list_item: F,
) -> Result<Vec<R>, Diagnostic>
where
    C: FnMut(&mut Context) -> Result<bool, Diagnostic>,
    F: Fn(&mut Context) -> Result<R, Diagnostic>,
{
    let mut v = vec![];
    loop {
        v.push(parse_list_item(context)?);
        if !parse_list_continue(context)? {
            break Ok(v);
        }
    }
}

// Parse a field name:
//      Field = <Identifier>
pub fn parse_field(context: &mut Context) -> Result<Field, Diagnostic> {
    parse_identifier(context)
}

// Parse a variable name:
//      Var = <Identifier>
pub fn parse_var(context: &mut Context) -> Result<Var, Diagnostic> {
    parse_identifier(context)
}

pub fn parse_file(
    files: &mut FilesSourceText,
    fname: Symbol,
) -> anyhow::Result<(Vec<Definition>, Diagnostics, FileHash, Vec<Token>)> {
    let mut diags = Diagnostics::new();
    let mut f = File::open(fname.as_str())
        .map_err(|err| std::io::Error::new(err.kind(), format!("{}: {}", err, fname)))?;
    let mut source_buffer = String::new();
    f.read_to_string(&mut source_buffer)?;
    let file_hash = FileHash::new(&source_buffer);
    let buffer = match verify_string(file_hash, &source_buffer) {
        Err(ds) => {
            diags.extend(ds);
            files.insert(file_hash, (fname, source_buffer));
            return Ok((vec![], diags, file_hash, vec![]));
        }
        Ok(()) => &source_buffer,
    };
    let (defs, tokens) = match parse_file_string(file_hash, buffer) {
        Ok((defs, tokens)) => (defs, tokens),
        Err(ds) => {
            diags.extend(ds);
            (vec![], vec![])
        }
    };
    files.insert(file_hash, (fname, source_buffer));
    Ok((defs, diags, file_hash, tokens))
}

/// Parse the `input` string as a file of Move source code and return the
/// result as either a pair of FileDefinition and doc comments or some Diagnostics. The `file` name
/// is used to identify source locations in error messages.
pub fn parse_file_string(
    file_hash: FileHash,
    input: &str,
) -> Result<(Vec<Definition>, Vec<Token>), Diagnostics> {
    let mut tokens = FidelityLexer::new(input, file_hash);
    let mut context = Context::new(&mut tokens);
    parse_definition(&mut context)
        .map_err(|e| Diagnostics::from(vec![e]))
        .map(|defs| (defs, context.tokens.get_tokens()))
}

#[cfg(test)]
mod test {
    use move_command_line_common::files::FileHash;

    use crate::parser::parsed_tree::ast::{
        Attributes, ParsedTree, SemicolonEnd, SequenceItem, SequenceItem_,
    };

    use super::{parse_attributes::parse_attributes, parse_tree, Context, FidelityLexer};

    #[test]
    fn test_parse_attribute() {
        let mut lexer = FidelityLexer::new("#[test_only,val=2,t(c=a::g,b=1)]", FileHash::empty());
        let mut context = Context::new(&mut lexer);
        let _ = context.tokens.advance();
        let result = parse_attributes(&mut context).unwrap();
        assert!(matches!(result, Attributes { .. }), "result: {:?}", result)
    }
    #[test]
    fn test_parse_const() {
        let mut lexer = FidelityLexer::new("const a: i32 = 123;", FileHash::empty());
        let mut context = Context::new(&mut lexer);
        let _ = context.tokens.advance();
        let result = parse_tree(&mut context).unwrap();
        assert!(
            matches!(
                result,
                ParsedTree::Sequence(SequenceItem {
                    value: SequenceItem_::Constant { .. },
                    ..
                })
            ),
            "result: {:?}",
            result
        )
    }
    #[test]
    fn test_parse_let() {
        let mut lexer = FidelityLexer::new("let a: i32 = 123;", FileHash::empty());
        let mut context = Context::new(&mut lexer);
        let _ = context.tokens.advance();
        let result = parse_tree(&mut context).unwrap();
        assert!(
            matches!(
                result,
                ParsedTree::Sequence(SequenceItem {
                    value: SequenceItem_::Bind { .. },
                    ..
                })
            ),
            "result: {:?}",
            result
        )
    }
    #[test]
    fn test_parse_use() {
        let mut lexer =
            FidelityLexer::new("use leading::mod::{mod1, mod2 as mod3};", FileHash::empty());
        let mut context = Context::new(&mut lexer);
        let _ = context.tokens.advance();
        let result = parse_tree(&mut context).unwrap();
        assert!(
            matches!(
                result,
                ParsedTree::Sequence(SequenceItem {
                    value: SequenceItem_::UseDecl { .. },
                    ..
                })
            ),
            "result: {:?}",
            result
        )
    }

    #[test]
    fn test_parse_friend() {
        let mut lexer = FidelityLexer::new("friend ident::ident2::ident3;", FileHash::empty());
        let mut context = Context::new(&mut lexer);
        let _ = context.tokens.advance();
        let result = parse_tree(&mut context).unwrap();
        assert!(
            matches!(
                result,
                ParsedTree::Sequence(SequenceItem {
                    value: SequenceItem_::FriendDecl { .. },
                    ..
                })
            ),
            "result: {:?}",
            result
        )
    }

    #[test]
    fn test_parse_struct() {
        let mut lexer = FidelityLexer::new(
            "public struct A has copy, move {field1: u32, field2: u16}",
            FileHash::empty(),
        );
        let mut context = Context::new(&mut lexer);
        let _ = context.tokens.advance();
        let result = parse_tree(&mut context).unwrap();
        assert!(
            matches!(result, ParsedTree::Struct { .. }),
            "result: {:?}",
            result
        )
    }

    #[test]
    fn test_parse_fun() {
        let mut lexer = FidelityLexer::new(
            "public fun do<foo>(param: type): (bar, foo){let a = 123;}",
            FileHash::empty(),
        );
        let mut context = Context::new(&mut lexer);
        let _ = context.tokens.advance();
        let result = parse_tree(&mut context).unwrap();
        assert!(
            matches!(result, ParsedTree::Function { .. }),
            "result: {:?}",
            result
        )
    }

    #[test]
    fn test_parse_exp() {
        let text = "loop{if (a>1){b=1+2*3;abort 1;} else {return 1};
            let c = 100;
            let d;
        };";
        let mut lexer = FidelityLexer::new(&text, FileHash::empty());
        let mut context = Context::new(&mut lexer);
        let _ = context.tokens.advance();
        let result = parse_tree(&mut context).unwrap();
        assert!(
            matches!(
                result,
                ParsedTree::Sequence(SequenceItem {
                    value: SequenceItem_::Exp(.., SemicolonEnd::IsSemicolonEnd(_)),
                    ..
                })
            ),
            "result: {:?}",
            result
        )
    }

    #[test]
    fn test_parse_spec() {
        let text = "spec schema b {
            pragma b;
            include AbortsIfNotCoreResource {addr: signer::address_of(account) };
            addr: address;
            aborts_if addr != @CoreResources with errors::REQUIRES_ADDRESS;
        }";
        let mut lexer = FidelityLexer::new(&text, FileHash::empty());
        let mut context = Context::new(&mut lexer);
        let _ = context.tokens.advance();
        let result = parse_tree(&mut context).unwrap();
        assert!(
            matches!(
                result,
                ParsedTree::Sequence(SequenceItem {
                    value: SequenceItem_::Spec(..),
                    ..
                })
            ),
            "result: {:?}",
            result
        )
    }
}
