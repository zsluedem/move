// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::{
    diag,
    diagnostics::Diagnostic,
    parser::{ast as T, parsed_tree::ast as P},
};

use super::{
    translate_attribute::tranlsate_vec_attributes, translate_constant::translate_constant,
    translate_friend::translate_friend, translate_function::translate_function,
    translate_spec::translate_spec_block, translate_struct::translate_struct,
    translate_token_to_leading_name_access, translate_token_to_name,
    translate_use::translate_use_decl, Context,
};

pub fn translate_module(
    context: &mut Context,
    ast: &P::PackageDefinition,
    module: &P::Module,
) -> Result<T::ModuleDefinition, Diagnostic> {
    let leading_comments = module.leading_comments(&ast.source_tokens);
    let loc = module.loc(&ast.source_tokens);
    context.insert_comments(loc.start(), leading_comments);
    let address = match &module.value().address {
        Some(addr) => Ok(Some(translate_token_to_leading_name_access(ast, &addr)?)),
        None => Ok(None),
    }?;
    let name = translate_module_name(ast, &module.value().name)?;
    let is_spec_module = module.value().is_spec_mod;
    let members = module
        .value()
        .body
        .iter()
        .map(|mem| translate_module_members(context, ast, mem))
        .collect::<Result<Vec<_>, _>>()?;
    let attributes = tranlsate_vec_attributes(ast, &module.value().attributes)?;
    Ok(T::ModuleDefinition {
        attributes,
        loc,
        address,
        name,
        is_spec_module,
        members,
    })
}
fn translate_module_name(
    ast: &P::PackageDefinition,
    name: &P::ParsedToken,
) -> Result<T::ModuleName, Diagnostic> {
    Ok(T::ModuleName(translate_token_to_name(ast, name)?))
}

fn translate_module_members(
    context: &mut Context,
    ast: &P::PackageDefinition,
    tree: &P::ParsedTree,
) -> Result<T::ModuleMember, Diagnostic> {
    match tree {
        P::ParsedTree::Function(func) => {
            let res = translate_function(context, ast, func)?;
            Ok(T::ModuleMember::Function(res))
        }
        P::ParsedTree::Struct(struct_) => {
            let res = translate_struct(context, ast, struct_)?;
            Ok(T::ModuleMember::Struct(res))
        }
        P::ParsedTree::Sequence(item) => match item.value() {
            P::SequenceItem_::UseDecl(use_) => {
                let res = translate_use_decl(ast, use_)?;
                Ok(T::ModuleMember::Use(res))
            }
            P::SequenceItem_::FriendDecl(friend) => {
                let res = translate_friend(ast, friend)?;
                Ok(T::ModuleMember::Friend(res))
            }
            P::SequenceItem_::Declare(decl) => {
                let loc = decl.loc(&ast.source_tokens);
                Err(diag!(
                    Declarations::InvalidLet,
                    (loc, "let declare is not allowed in module scope")
                ))
            }
            P::SequenceItem_::Bind(assign) => {
                let loc = assign.loc(&ast.source_tokens);
                Err(diag!(
                    Declarations::InvalidLet,
                    (loc, "let declare is not allowed in module scope")
                ))
            }
            P::SequenceItem_::Constant(contant) => {
                let res = translate_constant(context, ast, contant)?;
                Ok(T::ModuleMember::Constant(res))
            }
            P::SequenceItem_::Exp(e, _) => {
                let loc = e.loc(&ast.source_tokens);
                Err(diag!(
                    Declarations::InvalidExpression,
                    (loc, "expression is not allowed in module scope")
                ))
            }
            P::SequenceItem_::Spec(spec_block) => {
                let res = translate_spec_block(context, ast, spec_block)?;
                Ok(T::ModuleMember::Spec(res))
            }
        },
    }
}
