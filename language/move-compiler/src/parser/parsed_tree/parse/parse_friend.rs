// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::{
    diagnostics::Diagnostic,
    parser::{
        lexer::Tok,
        parsed_tree::ast::{Attributes, FriendDecl, ParsedTree, SequenceItem, SequenceItem_},
    },
};

use super::{parse_name_access_chain, Context};

pub fn parse_friend_decl(
    context: &mut Context,
    attributes: Vec<Attributes>,
) -> Result<SequenceItem_, Diagnostic> {
    context.tokens.consume_token(Tok::Friend)?;
    let friend = parse_name_access_chain(context, || "a friend declaration")?;
    context.tokens.consume_token(Tok::Semicolon)?;
    Ok(SequenceItem_::FriendDecl(FriendDecl { attributes, friend }))
}

// Parse a friend declaration:
//      FriendDecl =
//          "friend" <NameAccessChain> ";"
pub fn parse_friend(
    context: &mut Context,
    attributes: Vec<Attributes>,
) -> Result<ParsedTree, Diagnostic> {
    let token_start_loc = context.tokens.tokens_loc();
    let friend = parse_friend_decl(context, attributes)?;

    let token_end_loc = context.tokens.tokens_loc();
    let token_range = context.tokens.token_range(token_start_loc, token_end_loc);

    Ok(ParsedTree::Sequence(SequenceItem::new(friend, token_range)))
}
