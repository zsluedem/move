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

use super::{
    translate_attribute::tranlsate_vec_attributes, translate_exp::translate_exp,
    translate_token_to_name, translate_type::translate_type, Context,
};

pub fn translate_constant(
    context: &mut Context,
    ast: &P::PackageDefinition,
    constant: &P::ConstantDecl,
) -> Result<T::Constant, Diagnostic> {
    let comments = constant.constant.leading_comments(&ast.source_tokens);
    let loc = constant.constant.loc(&ast.source_tokens);
    context.insert_comments(loc.start(), comments);
    let constant_value = constant.constant.value();
    let signature = translate_type(ast, &constant_value.signature)?;
    let name = translate_constant_name(ast, &constant_value.name)?;
    let value = translate_exp(context, ast, &constant_value.exp)?;
    let attributes = tranlsate_vec_attributes(ast, &constant.attributes)?;
    Ok(T::Constant {
        attributes,
        loc,
        signature,
        name,
        value,
    })
}

fn translate_constant_name(
    ast: &P::PackageDefinition,
    name: &P::Name,
) -> Result<T::ConstantName, Diagnostic> {
    Ok(T::ConstantName(translate_token_to_name(ast, name)?))
}
