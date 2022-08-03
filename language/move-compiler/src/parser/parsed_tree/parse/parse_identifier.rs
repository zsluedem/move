// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::{
    diagnostics::Diagnostic,
    parser::{lexer::Tok, parsed_tree::ast::ParsedToken},
};

use super::Context;

// Parse an identifier:
//      Identifier = <IdentifierValue>
pub fn parse_identifier(context: &mut Context) -> Result<ParsedToken, Diagnostic> {
    if context.tokens.peek() != Tok::Identifier {
        return Err(context.tokens.unexpected_token_error("an identifier"));
    }
    let token = context.tokens.advance()?;
    Ok(token)
}
// Check for the identifier token with specified value and return an error if it does not match.
pub fn consume_identifier(context: &mut Context, value: &str) -> Result<ParsedToken, Diagnostic> {
    if context.tokens.peek() == Tok::Identifier && context.tokens.content() == value {
        context.tokens.advance()
    } else {
        let expected = format!("'{}'", value);
        Err(context.tokens.unexpected_token_error(&expected))
    }
}

pub fn match_identifier(context: &mut Context, value: &str) -> Result<bool, Diagnostic> {
    if context.tokens.peek() == Tok::Identifier && context.tokens.content() == value {
        context.tokens.advance()?;
        Ok(true)
    } else {
        Ok(false)
    }
}
