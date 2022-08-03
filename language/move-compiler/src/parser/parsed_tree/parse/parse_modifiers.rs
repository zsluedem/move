// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::{
    diag,
    diagnostics::Diagnostic,
    parser::{
        ast::ENTRY_MODIFIER,
        lexer::Tok,
        parsed_tree::ast::{Modifier, Modifier_, Modifiers, Visibility, Visibility_},
        syntax::make_loc,
    },
};

use super::Context;
use crate::parser::ast::Visibility as V;
// Parse module member modifiers: visiblility and native.
// The modifiers are also used for script-functions
//      ModuleMemberModifiers = <ModuleMemberModifier>*
//      ModuleMemberModifier = <Visibility> | "native"
// ModuleMemberModifiers checks for uniqueness, meaning each individual ModuleMemberModifier can
// appear only once
pub fn parse_module_member_modifiers(context: &mut Context) -> Result<Modifiers, Diagnostic> {
    let mut mods = vec![];
    loop {
        match context.tokens.peek() {
            Tok::Public => {
                let start_loc = context.tokens.tokens_loc();
                let visibility = parse_visibility(context)?;
                let end_loc = context.tokens.tokens_loc();
                mods.push(Modifier::new(
                    Modifier_::Visibility(visibility),
                    context.tokens.token_range(start_loc, end_loc),
                ))
            }
            Tok::Native => {
                let modifier = context.tokens.advance()?;
                mods.push(Modifier::new(Modifier_::Native, modifier.token_range))
            }
            Tok::Identifier if context.tokens.content() == ENTRY_MODIFIER => {
                let modifier = context.tokens.advance()?;
                mods.push(Modifier::new(Modifier_::Entry, modifier.token_range))
            }
            _ => break,
        }
    }
    Ok(mods)
}

// Parse a function visibility modifier:
//      Visibility = "public" ( "(" "script" | "friend" ")" )?
pub fn parse_visibility(context: &mut Context) -> Result<Visibility, Diagnostic> {
    let start_loc = context.tokens.start_loc();
    let start_tokens_loc = context.tokens.tokens_loc();
    context.tokens.consume_token(Tok::Public)?;
    let sub_public_vis = if context.tokens.match_token(Tok::LParen)? {
        let sub_token = context.tokens.peek();
        context.tokens.advance()?;
        if sub_token != Tok::RParen {
            context.tokens.consume_token(Tok::RParen)?;
        }
        Some(sub_token)
    } else {
        None
    };
    let end_tokens_loc = context.tokens.tokens_loc();
    // this loc will cover the span of 'public' or 'public(...)' in entirety
    let end_loc = context.tokens.previous_end_loc();
    // this loc will cover the span of 'public' or 'public(...)' in entirety
    let loc = make_loc(context.tokens.file_hash(), start_loc, end_loc);
    let vis = match sub_public_vis {
        None => Visibility_::Public,
        Some(Tok::Script) => Visibility_::Script,
        Some(Tok::Friend) => Visibility_::Friend,
        _ => {
            let msg = format!(
                "Invalid visibility modifier. Consider removing it or using '{}' or '{}'",
                V::PUBLIC,
                V::FRIEND
            );
            return Err(diag!(Syntax::UnexpectedToken, (loc, msg)));
        }
    };
    Ok(Visibility::new(
        vis,
        context.tokens.token_range(start_tokens_loc, end_tokens_loc),
    ))
}
