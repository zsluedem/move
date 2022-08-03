// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::{
    diag,
    diagnostics::Diagnostic,
    parser::{
        ast::{self as T, ENTRY_MODIFIER},
        parsed_tree::ast as P,
        syntax::Modifiers,
    },
};

use super::Context;

pub fn translate_modifiers(
    context: &mut Context,
    ast: &P::PackageDefinition,
    modifiers: &[P::Modifier],
) -> Result<Modifiers, Diagnostic> {
    let mut mods = Modifiers::empty();
    for m in modifiers.iter() {
        let loc = m.token_range.loc(&ast.source_tokens);
        match m.value() {
            P::Modifier_::Native => {
                if let Some(prev_loc) = mods.native {
                    let msg = "Duplicate 'native' modifier".to_string();
                    let prev_msg = "'native' modifier previously given here".to_string();
                    context.env.add_diag(diag!(
                        Declarations::DuplicateItem,
                        (loc, msg),
                        (prev_loc, prev_msg)
                    ))
                }
                mods.native = Some(loc);
            }
            P::Modifier_::Entry => {
                if let Some(prev_loc) = mods.entry {
                    let msg = format!("Duplicate '{}' modifier", ENTRY_MODIFIER);
                    let prev_msg = format!("'{}' modifier previously given here", ENTRY_MODIFIER);
                    context.env.add_diag(diag!(
                        Declarations::DuplicateItem,
                        (loc, msg),
                        (prev_loc, prev_msg)
                    ))
                }
                mods.entry = Some(loc);
            }
            P::Modifier_::Visibility(v) => {
                if let Some(prev_vis) = &mods.visibility {
                    let msg = "Duplicate visibility modifier".to_string();
                    let prev_msg = "Visibility modifier previously given here".to_string();
                    context.env.add_diag(diag!(
                        Declarations::DuplicateItem,
                        (loc, msg),
                        (prev_vis.loc().unwrap(), prev_msg),
                    ));
                }
                mods.visibility = Some(translate_visibility(&ast, v));
            }
        }
    }
    Ok(mods)
}

pub fn translate_visibility(
    ast: &P::PackageDefinition,
    visibility: &P::Visibility,
) -> T::Visibility {
    let loc = visibility.token_range.loc(&ast.source_tokens);
    match visibility.value() {
        P::Visibility_::Friend => T::Visibility::Friend(loc),
        P::Visibility_::Public => T::Visibility::Public(loc),
        P::Visibility_::Script => T::Visibility::Script(loc),
        P::Visibility_::Internal => T::Visibility::Internal,
    }
}
