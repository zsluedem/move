// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use move_ir_types::location::Loc;

use crate::{
    diag,
    diagnostics::Diagnostic,
    parser::{
        ast::{self as T},
        parsed_tree::ast::{self as P},
        syntax::Modifiers,
    },
    shared::Identifier,
};

use super::{
    spanned,
    translate_attribute::tranlsate_vec_attributes,
    translate_exp::translate_exp_sequence,
    translate_modifiers::translate_modifiers,
    translate_name_access_chain, translate_token_to_name,
    translate_type::{translate_type, translate_type_parameter},
    translate_var, Context,
};

pub fn translate_function(
    context: &mut Context,
    ast: &P::PackageDefinition,
    function: &P::Function,
) -> Result<T::Function, Diagnostic> {
    let leading_comments = function.leading_comments(&ast.source_tokens);
    let loc = function.loc(&ast.source_tokens);
    context.insert_comments(loc.start(), leading_comments);
    let function_content = function.value();
    let mods = translate_modifiers(context, ast, &function_content.modifiers[..])?;
    let Modifiers {
        visibility: visibility_,
        mut entry,
        ..
    } = mods;
    if let Some(T::Visibility::Script(vloc)) = visibility_ {
        let msg = format!(
            "'{script}' is deprecated in favor of the '{entry}' modifier. \
            Replace with '{public} {entry}'",
            script = T::Visibility::SCRIPT,
            public = T::Visibility::PUBLIC,
            entry = T::ENTRY_MODIFIER,
        );
        context
            .env
            .add_diag(diag!(Uncategorized::DeprecatedWillBeRemoved, (vloc, msg,)));
        if entry.is_none() {
            entry = Some(vloc)
        }
    }
    let visibility = visibility_.unwrap_or(T::Visibility::Internal);
    let name = translate_function_name(ast, &function_content.name)?;
    let signature = translate_function_signature(ast, &function_content.signatures, name.loc())?;
    let acquires = function_content
        .acquires
        .iter()
        .map(|a| translate_name_access_chain(ast, a))
        .collect::<Result<Vec<_>, _>>()?;
    let body = translate_function_body(context, ast, &function_content.body)?;
    let attributes = tranlsate_vec_attributes(ast, &function_content.attributes)?;
    Ok(T::Function {
        attributes,
        loc,
        visibility,
        entry,
        signature,
        acquires,
        name,
        body,
    })
}

pub fn translate_function_body(
    context: &mut Context,
    ast: &P::PackageDefinition,
    function: &P::FunctionBody,
) -> Result<T::FunctionBody, Diagnostic> {
    let loc = function.loc(&ast.source_tokens);
    if function.value().is_native {
        Ok(spanned(loc, T::FunctionBody_::Native))
    } else {
        let body = translate_exp_sequence(context, ast, &function.value().body)?;
        Ok(spanned(loc, T::FunctionBody_::Defined(body)))
    }
}

pub fn translate_function_name(
    ast: &P::PackageDefinition,
    token: &P::Name,
) -> Result<T::FunctionName, Diagnostic> {
    let name = translate_token_to_name(ast, token)?;
    Ok(T::FunctionName(name))
}

pub fn translate_function_signature(
    ast: &P::PackageDefinition,
    signature: &P::FunctionSignature,
    function_name_loc: Loc,
) -> Result<T::FunctionSignature, Diagnostic> {
    let type_parameters = translate_type_parameter(ast, &signature.type_parameters)?;

    let parameters = signature
        .parameters
        .iter()
        .map(|(v, t)| {
            let var = translate_var(ast, v)?;
            let type_ = translate_type(ast, t)?;
            Ok((var, type_))
        })
        .collect::<Result<Vec<_>, _>>()?;

    let return_type = match &signature.return_type {
        Some(t) => translate_type(ast, t),
        None => Ok(spanned(function_name_loc, T::Type_::Unit)),
    }?;
    Ok(T::FunctionSignature {
        type_parameters,
        parameters,
        return_type,
    })
}
