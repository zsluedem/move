// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

//**************************************************************************************************
// Scripts
//**************************************************************************************************

use crate::{
    diagnostics::Diagnostic,
    parser::{
        lexer::Tok,
        parsed_tree::ast::{Attributes, Definition, Script, Script_},
    },
};

use super::{parse_tree, Context};

// Parse a script:
//      Script =
//          "script" "{"
//              (<Attributes> <UseDecl>)*
//              (<Attributes> <ConstantDecl>)*
//              <Attributes> <DocComments> <ModuleMemberModifiers> <FunctionDecl>
//              (<Attributes> <SpecBlock>)*
//          "}"
fn parse_script_decl(
    context: &mut Context,
    attributes: Vec<Attributes>,
) -> Result<Script, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    context.tokens.consume_token(Tok::Script)?;
    context.tokens.consume_token(Tok::LBrace)?;

    let mut body = vec![];
    while context.tokens.peek() != Tok::RBrace {
        body.push(parse_tree(context)?)
    }
    context.tokens.consume_token(Tok::RBrace)?;
    let end_loc = context.tokens.tokens_loc();
    let token_range = context.tokens.token_range(start_loc, end_loc);
    Ok(Script::new(
        Script_ {
            attributes,
            members: body,
        },
        token_range,
    ))
}
pub fn parse_script(
    context: &mut Context,
    attributes: Vec<Attributes>,
) -> Result<Definition, Diagnostic> {
    let tree = parse_script_decl(context, attributes)?;

    Ok(Definition::Script(tree))
}
