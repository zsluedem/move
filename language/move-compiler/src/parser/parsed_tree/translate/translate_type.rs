// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::{diagnostics::Diagnostic, shared::Name};

use super::{spanned, translate_ability, translate_name_access_chain, translate_token_to_name};
use crate::parser::{ast as T, parsed_tree::ast as P};

pub fn translate_type(ast: &P::PackageDefinition, type_: &P::Type) -> Result<T::Type, Diagnostic> {
    let loc = type_.loc(&ast.source_tokens);
    match type_.value() {
        P::Type_::Apply(names, types) => {
            let name_chains = translate_name_access_chain(ast, names)?;
            let typ = types
                .iter()
                .map(|t| translate_type(ast, t))
                .collect::<Result<Vec<T::Type>, _>>()?;
            Ok(spanned(loc, T::Type_::Apply(Box::new(name_chains), typ)))
        }
        P::Type_::Ref(is_mute, typ) => {
            let ty = translate_type(ast, typ)?;
            Ok(spanned(loc, T::Type_::Ref(*is_mute, Box::new(ty))))
        }
        P::Type_::Fun(typ1, typ2) => {
            let para_type = typ1
                .iter()
                .map(|t| translate_type(ast, t))
                .collect::<Result<Vec<T::Type>, _>>()?;
            let res_type = translate_type(ast, typ2)?;
            Ok(spanned(loc, T::Type_::Fun(para_type, Box::new(res_type))))
        }
        P::Type_::Sequance(types) => {
            if types.is_empty() {
                Ok(spanned(loc, T::Type_::Unit))
            } else {
                let typ = types
                    .iter()
                    .map(|t| translate_type(ast, t))
                    .collect::<Result<Vec<T::Type>, _>>()?;
                Ok(spanned(loc, T::Type_::Multiple(typ)))
            }
        }
    }
}

pub fn translate_type_parameter(
    ast: &P::PackageDefinition,
    type_parameters: &[(P::Name, Vec<P::Ability>)],
) -> Result<Vec<(Name, Vec<T::Ability>)>, Diagnostic> {
    type_parameters
        .iter()
        .map(|(n, a)| {
            let name = translate_token_to_name(ast, n)?;
            let abilities = a
                .iter()
                .map(|ability| translate_ability(ast, ability))
                .collect::<Result<Vec<_>, _>>()?;
            Ok((name, abilities))
        })
        .collect::<Result<Vec<_>, _>>()
}

pub fn translate_optional_types(
    ast: &P::PackageDefinition,
    type_opt: &Option<Vec<P::Type>>,
) -> Result<Option<Vec<T::Type>>, Diagnostic> {
    match type_opt {
        None => Ok(None),
        Some(types) => {
            let res = types
                .iter()
                .map(|t| translate_type(ast, t))
                .collect::<Result<Vec<_>, _>>();
            match res {
                Ok(r) => Ok(Some(r)),
                Err(e) => Err(e),
            }
        }
    }
}

pub fn translate_optional_type(
    ast: &P::PackageDefinition,
    type_opt: &Option<P::Type>,
) -> Result<Option<T::Type>, Diagnostic> {
    match type_opt {
        None => Ok(None),
        Some(type_) => {
            let res = translate_type(ast, type_);
            match res {
                Ok(r) => Ok(Some(r)),
                Err(e) => Err(e),
            }
        }
    }
}
