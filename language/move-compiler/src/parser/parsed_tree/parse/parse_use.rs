// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::{
    diagnostics::Diagnostic,
    parser::{
        lexer::Tok,
        parsed_tree::ast::{
            Attributes, ModuleIdent, Name, ParsedToken, ParsedTree, SequenceItem, SequenceItem_,
            Use, UseDecl,
        },
    },
};

use super::{parse_comma_list, parse_identifier, parse_leading_name_access, Context};

pub fn parse_use(
    context: &mut Context,
    attributes: Vec<Attributes>,
) -> Result<ParsedTree, Diagnostic> {
    let token_start_loc = context.tokens.tokens_loc();
    let use_ = parse_use_decl(context, attributes)?;
    let token_end_loc = context.tokens.tokens_loc();
    let token_range = context.tokens.token_range(token_start_loc, token_end_loc);
    Ok(ParsedTree::Sequence(SequenceItem::new(
        SequenceItem_::UseDecl(use_),
        token_range,
    )))
}

// Parse a use declaration:
//      UseDecl =
//          "use" <ModuleIdent> <UseAlias> ";" |
//          "use" <ModuleIdent> :: <UseMember> ";" |
//          "use" <ModuleIdent> :: "{" Comma<UseMember> "}" ";"
pub fn parse_use_decl(
    context: &mut Context,
    attributes: Vec<Attributes>,
) -> Result<UseDecl, Diagnostic> {
    context.tokens.consume_token(Tok::Use)?;
    let ident = parse_module_ident(context)?;
    let alias_opt = parse_use_alias(context)?;
    let use_ = match (&alias_opt, context.tokens.peek()) {
        (None, Tok::ColonColon) => {
            context.tokens.consume_token(Tok::ColonColon)?;
            let sub_uses = match context.tokens.peek() {
                Tok::LBrace => parse_comma_list(
                    context,
                    Tok::LBrace,
                    Tok::RBrace,
                    parse_use_member,
                    "a module member alias",
                )?,
                _ => vec![parse_use_member(context)?],
            };
            Use::Members(ident, sub_uses)
        }
        _ => Use::Module(ident, alias_opt),
    };
    context.tokens.consume_token(Tok::Semicolon)?;
    Ok(UseDecl { attributes, use_ })
}

// Parse an 'as' use alias:
//      UseAlias = ("as" <Identifier>)?
fn parse_use_alias(context: &mut Context) -> Result<Option<Name>, Diagnostic> {
    Ok(if context.tokens.peek() == Tok::As {
        context.tokens.advance()?;
        Some(parse_identifier(context)?)
    } else {
        None
    })
}

// Parse a module identifier:
//      ModuleIdent = <LeadingNameAccess> "::" <ModuleName>
fn parse_module_ident(context: &mut Context) -> Result<ModuleIdent, Diagnostic> {
    let start_loc = context.tokens.start_loc();
    let address = parse_leading_name_access(context)?;

    context.tokens.consume_token_(
        Tok::ColonColon,
        start_loc,
        " after an address in a module identifier",
    )?;
    let module = parse_module_name(context)?;
    Ok(ModuleIdent { address, module })
}
// Parse an alias for a module member:
//      UseMember = <Identifier> <UseAlias>
fn parse_use_member(context: &mut Context) -> Result<(Name, Option<Name>), Diagnostic> {
    let member = parse_identifier(context)?;
    let alias_opt = parse_use_alias(context)?;
    Ok((member, alias_opt))
}

// Parse a module name:
//      ModuleName = <Identifier>
pub fn parse_module_name(context: &mut Context) -> Result<ParsedToken, Diagnostic> {
    parse_identifier(context)
}
