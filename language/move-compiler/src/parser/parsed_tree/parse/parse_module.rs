// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::{
    diagnostics::Diagnostic,
    parser::{
        lexer::Tok,
        parsed_tree::ast::{Attributes, Definition, Module, Module_},
    },
};

use super::{parse_leading_name_access, parse_tree, parse_use::parse_module_name, Context};

// Parse a module:
//      Module =
//          <DocComments> ( "spec" | "module") (<LeadingNameAccess>::)?<ModuleName> "{"
//              ( <Attributes>
//                  ( <UseDecl> | <FriendDecl> | <SpecBlock> |
//                    <DocComments> <ModuleMemberModifiers>
//                        (<ConstantDecl> | <StructDecl> | <FunctionDecl>) )
//                  )
//              )*
//          "}"
pub fn parse_module_decl(
    context: &mut Context,
    attributes: Vec<Attributes>,
) -> Result<Module, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    let is_spec_mod = if context.tokens.peek() == Tok::Spec {
        context.tokens.advance()?;
        true
    } else {
        context.tokens.consume_token(Tok::Module)?;
        false
    };
    let leading = parse_leading_name_access(context)?;
    let (name, address) = if context.tokens.match_token(Tok::ColonColon)? {
        (parse_module_name(context)?, Some(leading))
    } else {
        (leading, None)
    };

    context.tokens.consume_token(Tok::LBrace)?;

    let mut body = vec![];
    while context.tokens.peek() != Tok::RBrace {
        body.push(parse_tree(context)?)
    }
    context.tokens.consume_token(Tok::RBrace)?;
    let end_loc = context.tokens.tokens_loc();
    let token_range = context.tokens.token_range(start_loc, end_loc);
    let def = Module::new(
        Module_ {
            attributes,
            address,
            name,
            body,
            is_spec_mod,
        },
        token_range,
    );

    Ok(def)
}

pub fn parse_module(
    context: &mut Context,
    attributes: Vec<Attributes>,
) -> Result<Definition, Diagnostic> {
    let tree = parse_module_decl(context, attributes)?;
    Ok(Definition::Module(tree))
}
