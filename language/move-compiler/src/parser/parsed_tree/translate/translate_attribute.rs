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

use super::{spanned, translate_name_access_chain, translate_token_to_name, translate_value};

pub fn tranlsate_vec_attributes(
    ast: &P::PackageDefinition,
    attrs: &[P::Attributes],
) -> Result<Vec<T::Attributes>, Diagnostic> {
    attrs
        .iter()
        .map(|a| translate_attributes(ast, a))
        .collect::<Result<Vec<_>, _>>()
}

pub fn translate_attributes(
    ast: &P::PackageDefinition,
    attrs: &P::Attributes,
) -> Result<T::Attributes, Diagnostic> {
    let loc = attrs.loc(&ast.source_tokens);
    let target_attrs: Result<Vec<T::Attribute>, Diagnostic> = attrs
        .value()
        .iter()
        .map(|a| {
            let loc = a.loc(&ast.source_tokens);
            let attr_ = match a.value() {
                P::Attribute_::Name(n) => {
                    let name = translate_token_to_name(&ast, &n)?;
                    T::Attribute_::Name(name)
                }
                P::Attribute_::Assigned(n, value) => {
                    let name = translate_token_to_name(&ast, &n)?;
                    let values = translate_attribute_value(&ast, &value)?;

                    T::Attribute_::Assigned(name, Box::new(values))
                }
                P::Attribute_::Parameterized(n, attributes) => {
                    let name = translate_token_to_name(&ast, &n)?;
                    let attributes_ = translate_attributes(&ast, &attributes)?;
                    T::Attribute_::Parameterized(name, attributes_)
                }
            };
            Ok(spanned(loc, attr_))
        })
        .collect();
    Ok(spanned(loc, target_attrs?))
}

fn translate_attribute_value(
    ast: &P::PackageDefinition,
    attr_value: &P::AttributeValue,
) -> Result<T::AttributeValue, Diagnostic> {
    match attr_value {
        P::AttributeValue::Value(v) => {
            let loc = v.loc(&ast.source_tokens);
            Ok(spanned(
                loc,
                T::AttributeValue_::Value(translate_value(&ast, &v)?),
            ))
        }
        P::AttributeValue::ModuleAccess(n) => {
            let names = translate_name_access_chain(&ast, &n)?;
            Ok(spanned(names.loc, T::AttributeValue_::ModuleAccess(names)))
        }
    }
}
