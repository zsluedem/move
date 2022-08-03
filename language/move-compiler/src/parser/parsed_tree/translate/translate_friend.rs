// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::{
    diagnostics::Diagnostic,
    parser::{
        ast::{self as T},
        parsed_tree::ast::{self as P},
    },
};

use super::{translate_attribute::tranlsate_vec_attributes, translate_name_access_chain};

pub fn translate_friend(
    ast: &P::PackageDefinition,
    friend: &P::FriendDecl,
) -> Result<T::FriendDecl, Diagnostic> {
    let loc = friend.friend.loc(&ast.source_tokens);
    let attributes = tranlsate_vec_attributes(ast, &friend.attributes)?;
    let friend = translate_name_access_chain(ast, &friend.friend)?;
    Ok(T::FriendDecl {
        attributes,
        loc,
        friend,
    })
}
