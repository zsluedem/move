// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::{
    diagnostics::Diagnostic,
    parser::{ast as T, parsed_tree::ast as P},
    shared::Name,
};

use super::{
    spanned, spanned_between, translate_attribute::tranlsate_vec_attributes,
    translate_token_to_leading_name_access, translate_token_to_name,
};

pub fn translate_use_decl(
    ast: &P::PackageDefinition,
    use_: &P::UseDecl,
) -> Result<T::UseDecl, Diagnostic> {
    let uses_ = translate_use(&ast, &use_.use_)?;
    let attributes = tranlsate_vec_attributes(&ast, &use_.attributes)?;
    Ok(T::UseDecl {
        attributes,
        use_: uses_,
    })
}

pub fn translate_use(ast: &P::PackageDefinition, use_: &P::Use) -> Result<T::Use, Diagnostic> {
    match use_ {
        P::Use::Module(ident, name) => {
            let ident_ = translate_module_ident(&ast, &ident)?;
            let name_ = match name {
                Some(n) => translate_token_to_module_name(&ast, n).map(Some),
                None => Ok(None),
            }?;
            Ok(T::Use::Module(ident_, name_))
        }
        P::Use::Members(ident, names) => {
            let ident_ = translate_module_ident(&ast, &ident)?;
            let names_: Result<Vec<(Name, Option<Name>)>, Diagnostic> = names
                .iter()
                .map(|(name, name_opt)| match name_opt {
                    Some(n) => {
                        let lead_name = translate_token_to_name(&ast, &name)?;
                        translate_token_to_name(&ast, &n).map(|n| (lead_name, Some(n)))
                    }
                    None => {
                        let lead_name = translate_token_to_name(&ast, &name)?;
                        Ok((lead_name, None))
                    }
                })
                .collect();
            Ok(T::Use::Members(ident_, names_?))
        }
    }
}

fn translate_token_to_module_name(
    ast: &P::PackageDefinition,
    name: &P::Name,
) -> Result<T::ModuleName, Diagnostic> {
    let name = translate_token_to_name(&ast, &name)?;
    Ok(T::ModuleName(name))
}

fn translate_module_ident(
    ast: &P::PackageDefinition,
    module: &P::ModuleIdent,
) -> Result<T::ModuleIdent, Diagnostic> {
    let loc = spanned_between(&module.address, &module.module);
    let address = translate_token_to_leading_name_access(&ast, &module.address)?;
    let module = translate_token_to_module_name(&ast, &module.module)?;
    Ok(spanned(loc, T::ModuleIdent_ { address, module }))
}
