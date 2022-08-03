// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::{
    diagnostics::Diagnostic,
    parser::{
        ast::{self as T},
        parsed_tree::{
            ast::{self as P},
            translate::translate_type::translate_optional_type,
        },
    },
    shared::Identifier,
};

use super::{
    spanned, translate_exp::translate_exp, translate_field, translate_name_access_chain,
    translate_type::translate_optional_types, translate_var, Context,
};

pub fn translate_let_declare(
    ast: &P::PackageDefinition,
    decl: &P::LetDeclare,
) -> Result<T::SequenceItem_, Diagnostic> {
    let decl_content = decl.value();
    let bind_res = translate_bind_list(ast, &decl_content.var)?;
    let type_res = translate_optional_type(ast, &decl_content.type_)?;
    Ok(T::SequenceItem_::Declare(bind_res, type_res))
}

pub fn translate_let_assign(
    context: &mut Context,
    ast: &P::PackageDefinition,
    assign: &P::LetAssign,
) -> Result<T::SequenceItem_, Diagnostic> {
    let bind_res = translate_bind_list(ast, &assign.value().var)?;
    let type_res = translate_optional_type(ast, &assign.value().type_)?;
    let exp_res = translate_exp(context, ast, &assign.value().exp)?;
    Ok(T::SequenceItem_::Bind(
        bind_res,
        type_res,
        Box::new(exp_res),
    ))
}

pub fn translate_bind_list(
    ast: &P::PackageDefinition,
    bind: &P::BindList,
) -> Result<T::BindList, Diagnostic> {
    let loc = bind.loc(&ast.source_tokens);
    let binds = bind
        .value()
        .iter()
        .map(|b| translate_bind(ast, b))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(spanned(loc, binds))
}

fn translate_bind(ast: &P::PackageDefinition, bind: &P::Bind) -> Result<T::Bind, Diagnostic> {
    let loc = bind.loc(&ast.source_tokens);
    let bind_res = match bind.value() {
        P::Bind_::Var(v) => Ok(T::Bind_::Var(translate_var(ast, v)?)),
        P::Bind_::Unpack(name, type_opt, fields) => {
            let name_res = translate_name_access_chain(ast, name)?;
            let type_res = translate_optional_types(ast, type_opt)?;
            let fields_res = fields
                .iter()
                .map(|(f, bi)| translate_bind_field(ast, f, bi))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(T::Bind_::Unpack(Box::new(name_res), type_res, fields_res))
        }
    }?;
    Ok(spanned(loc, bind_res))
}

fn translate_bind_field(
    ast: &P::PackageDefinition,
    field: &P::Field,
    bind: &Option<P::Bind>,
) -> Result<(T::Field, T::Bind), Diagnostic> {
    let field_res = translate_field(ast, field)?;
    let bind_res = match bind {
        Some(b) => translate_bind(ast, b),
        None => {
            let v = T::Var(field_res.0);
            Ok(spanned(v.loc(), T::Bind_::Var(v)))
        }
    }?;
    Ok((field_res, bind_res))
}
