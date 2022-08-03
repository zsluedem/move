// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::{
    diagnostics::Diagnostic,
    parser::{
        lexer::Tok,
        parsed_tree::ast::{
            Attributes, Function, FunctionBody, FunctionBody_, FunctionSignature, Function_,
            Modifiers, ParsedTree,
        },
    },
};

use super::{
    parse_comma_list,
    parse_exp::parse_sequence_block,
    parse_identifier::parse_identifier,
    parse_name_access_chain,
    parse_spec::parse_parameter,
    parse_type::{parse_optional_type_parameters, parse_type},
    Context,
};

// Parse a function declaration:
//      FunctionDecl =
//          "fun"
//          <FunctionDefName> "(" Comma<Parameter> ")"
//          (":" <Type>)?
//          ("acquires" <NameAccessChain> ("," <NameAccessChain>)*)?
//          ("{" <Sequence> "}" | ";")
//
fn parse_function_decl(
    modifiers: Modifiers,
    context: &mut Context,
    attributes: Vec<Attributes>,
) -> Result<Function, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();

    // "fun" <FunctionDefName>
    context.tokens.consume_token(Tok::Fun)?;
    let name = parse_identifier(context)?;
    let type_parameters = parse_optional_type_parameters(context)?;

    // "(" Comma<Parameter> ")"
    let parameters = parse_comma_list(
        context,
        Tok::LParen,
        Tok::RParen,
        parse_parameter,
        "a function parameter",
    )?;

    // (":" <Type>)?
    let return_type = if context.tokens.match_token(Tok::Colon)? {
        Some(parse_type(context)?)
    } else {
        None
    };

    // ("acquires" (<NameAccessChain> ",")* <NameAccessChain> ","?
    let mut acquires = vec![];
    if context.tokens.match_token(Tok::Acquires)? {
        let follows_acquire = |tok| matches!(tok, Tok::Semicolon | Tok::LBrace);
        loop {
            acquires.push(parse_name_access_chain(context, || {
                "a resource struct name"
            })?);
            if follows_acquire(context.tokens.peek()) {
                break;
            }
            context.tokens.consume_token(Tok::Comma)?;
            if follows_acquire(context.tokens.peek()) {
                break;
            }
        }
    }

    let body_start_loc = context.tokens.tokens_loc();
    let body = if context.tokens.match_token(Tok::Semicolon)? {
        let body_end_loc = context.tokens.tokens_loc();

        FunctionBody::new(
            FunctionBody_ {
                body: vec![],
                is_native: true,
            },
            context.tokens.token_range(body_start_loc, body_end_loc),
        )
    } else {
        let seq = parse_sequence_block(context)?;
        let body_end_loc = context.tokens.tokens_loc();
        FunctionBody::new(
            FunctionBody_ {
                body: seq,
                is_native: false,
            },
            context.tokens.token_range(body_start_loc, body_end_loc),
        )
    };

    let signatures = FunctionSignature {
        type_parameters,
        parameters,
        return_type,
    };
    let end_loc = context.tokens.tokens_loc();
    let token_range = context.tokens.token_range(start_loc, end_loc);
    Ok(Function::new(
        Function_ {
            attributes,
            modifiers,
            signatures,
            acquires,
            name,
            body,
        },
        token_range,
    ))
}
pub fn parse_function(
    modifiers: Modifiers,
    context: &mut Context,
    attributes: Vec<Attributes>,
) -> Result<ParsedTree, Diagnostic> {
    let tree = parse_function_decl(modifiers, context, attributes)?;

    Ok(ParsedTree::Function(tree))
}
