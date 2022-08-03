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
    translate_attribute::tranlsate_vec_attributes, translate_module::translate_module,
    translate_token_to_leading_name_access, Context,
};

pub fn translate_address(
    context: &mut Context,
    ast: &P::PackageDefinition,
    address: &P::Address,
) -> Result<T::AddressDefinition, Diagnostic> {
    let loc = address.loc(&ast.source_tokens);
    let attributes = tranlsate_vec_attributes(ast, &address.value().attributes)?;
    let addr = translate_token_to_leading_name_access(ast, &address.value().address)?;
    let modules = address
        .value()
        .modules
        .iter()
        .map(|m| translate_module(context, ast, m))
        .collect::<Result<Vec<_>, _>>()?;

    Ok(T::AddressDefinition {
        attributes,
        loc,
        addr,
        modules,
    })
}
