// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::{
    diag,
    diagnostics::Diagnostic,
    parser::{
        ast::{self as T, Visibility, ENTRY_MODIFIER},
        parsed_tree::ast as P,
        syntax::Modifiers,
    },
};

use super::{
    translate_ability, translate_attribute::tranlsate_vec_attributes, translate_field,
    translate_modifiers::translate_modifiers, translate_token_to_name,
    translate_type::translate_type, Context,
};

pub fn translate_struct(
    context: &mut Context,
    ast: &P::PackageDefinition,
    struct_: &P::Struct,
) -> Result<T::StructDefinition, Diagnostic> {
    let comments = struct_.leading_comments(&ast.source_tokens);
    let loc = struct_.loc(&ast.source_tokens);
    context.insert_comments(loc.start(), comments);
    let struct_content = struct_.value();
    let mods = translate_modifiers(context, ast, &struct_content.modifiers[..])?;
    let attributes = tranlsate_vec_attributes(ast, &struct_content.attributes)?;
    let Modifiers {
        visibility,
        entry,
        native,
    } = mods;
    if let Some(vis) = visibility {
        let msg = format!(
            "Invalid struct declaration. Structs cannot have visibility modifiers as they are \
             always '{}'",
            Visibility::PUBLIC
        );
        context
            .env
            .add_diag(diag!(Syntax::InvalidModifier, (vis.loc().unwrap(), msg)));
    }
    if let Some(entry_loc) = entry {
        let msg = format!(
            "Invalid constant declaration. '{}' is used only on functions",
            ENTRY_MODIFIER
        );
        context
            .env
            .add_diag(diag!(Syntax::InvalidModifier, (entry_loc, msg)));
    }

    let struct_name = translate_struct_name(&ast, &struct_content.name)?;

    let abilities = struct_content
        .abilities
        .iter()
        .map(|a| translate_ability(ast, a))
        .collect::<Result<Vec<_>, _>>()?;

    let type_parameters = translate_struct_type_parameter(ast, &struct_content.type_parameters)?;

    let fields = match native {
        Some(loc) => Ok(T::StructFields::Native(loc)),
        None => {
            let fields_target = struct_content
                .fields
                .members
                .iter()
                .map(|(field, type_)| {
                    let f = translate_field(ast, field)?;
                    let ty = translate_type(ast, type_)?;
                    Ok((f, ty))
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(T::StructFields::Defined(fields_target))
        }
    }?;

    Ok(T::StructDefinition {
        attributes,
        loc,
        abilities,
        name: struct_name,
        type_parameters,
        fields,
    })
}

fn translate_struct_name(
    ast: &P::PackageDefinition,
    token: &P::Name,
) -> Result<T::StructName, Diagnostic> {
    let name = translate_token_to_name(ast, token)?;
    Ok(T::StructName(name))
}

fn translate_struct_type_parameter(
    ast: &P::PackageDefinition,
    types: &[P::StructTypeParameter],
) -> Result<Vec<T::StructTypeParameter>, Diagnostic> {
    types
        .iter()
        .map(|type_| {
            let name = translate_token_to_name(&ast, &type_.name)?;
            let constraints = type_
                .constraints
                .iter()
                .map(|c| translate_ability(ast, c))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(T::StructTypeParameter {
                is_phantom: type_.is_phantom,
                name,
                constraints,
            })
        })
        .collect()
}
