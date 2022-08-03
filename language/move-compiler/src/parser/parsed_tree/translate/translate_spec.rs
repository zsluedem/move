// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use std::vec;

use crate::{
    diagnostics::Diagnostic,
    parser::{
        ast::{self as T},
        lexer::Tok,
        parsed_tree::ast::{self as P},
    },
    shared::Identifier,
};

use super::{
    spanned,
    translate_attribute::tranlsate_vec_attributes,
    translate_exp::translate_exp,
    translate_function::{
        translate_function_body, translate_function_name, translate_function_signature,
    },
    translate_modifiers::translate_visibility,
    translate_name_access_chain, translate_token_to_name,
    translate_type::{translate_type, translate_type_parameter},
    translate_use::translate_use_decl,
    translate_value, unexpected_token_error, Context,
};

pub fn translate_spec_block(
    context: &mut Context,
    ast: &P::PackageDefinition,
    spec_block: &P::SpecBlock,
) -> Result<T::SpecBlock, Diagnostic> {
    let comments = spec_block.leading_comments(&ast.source_tokens);
    let loc = spec_block.loc(&ast.source_tokens);
    context.insert_comments(loc.start(), comments);
    let uses = spec_block
        .value()
        .uses
        .iter()
        .map(|use_| translate_use_decl(ast, use_))
        .collect::<Result<Vec<_>, _>>()?;
    let target = translate_spec_target(ast, &spec_block.value().target)?;
    let members = spec_block
        .value
        .members
        .iter()
        .map(|m| translate_spec_member(context, ast, m))
        .collect::<Result<Vec<_>, _>>()?;
    let attributes = tranlsate_vec_attributes(ast, &spec_block.value().attributes)?;
    Ok(spanned(
        loc,
        T::SpecBlock_ {
            attributes,
            target,
            uses,
            members,
        },
    ))
}

fn translate_spec_condition_kind(
    context: &mut Context,
    ast: &P::PackageDefinition,
    cond: &P::SpecConditionKind,
) -> Result<T::SpecBlockMember_, Diagnostic> {
    match cond.value() {
        P::SpecConditionKind_::SingleExpCondition {
            kind,
            properties,
            exp,
        } => {
            let properties_res = properties
                .iter()
                .map(|p| translate_progma_property(ast, p))
                .collect::<Result<Vec<_>, _>>()?;
            let exp_res = translate_exp(context, ast, exp)?;
            let kind_loc = kind.loc(&ast.source_tokens);
            let res_func = |k: T::SpecConditionKind_| {
                Ok(T::SpecBlockMember_::Condition {
                    kind: spanned(kind_loc, k),
                    properties: properties_res,
                    exp: exp_res,
                    additional_exps: vec![],
                })
            };
            match kind.value() {
                P::SingleSpecCondition::Assert => res_func(T::SpecConditionKind_::Assert),
                P::SingleSpecCondition::Assume => res_func(T::SpecConditionKind_::Assume),
                P::SingleSpecCondition::Ensures => res_func(T::SpecConditionKind_::Ensures),
                P::SingleSpecCondition::Requires => res_func(T::SpecConditionKind_::Requires),
                P::SingleSpecCondition::Decreases => res_func(T::SpecConditionKind_::Decreases),
                P::SingleSpecCondition::SucceedsIf => res_func(T::SpecConditionKind_::SucceedsIf),
            }
        }
        P::SpecConditionKind_::AbortsIf {
            loc,
            properties,
            exp,
            with_exp,
        } => {
            let properties_res = properties
                .iter()
                .map(|p| translate_progma_property(ast, p))
                .collect::<Result<Vec<_>, _>>()?;
            let exp_res = translate_exp(context, ast, exp)?;
            let with_exp_res = match with_exp {
                Some(e) => Ok(vec![translate_exp(context, ast, e)?]),
                None => Ok(vec![]),
            }?;
            let keyword_loc = loc.loc(&ast.source_tokens);
            Ok(T::SpecBlockMember_::Condition {
                kind: spanned(keyword_loc, T::SpecConditionKind_::AbortsIf),
                properties: properties_res,
                exp: exp_res,
                additional_exps: with_exp_res,
            })
        }
        P::SpecConditionKind_::CommaExpCondition {
            kind,
            properties,
            exps,
        } => {
            let kind_loc = kind.loc(&ast.source_tokens);
            let properties_res = properties
                .iter()
                .map(|p| translate_progma_property(ast, p))
                .collect::<Result<Vec<_>, _>>()?;
            let exps_res = exps
                .iter()
                .map(|e| translate_exp(context, ast, e))
                .collect::<Result<Vec<_>, _>>()?;
            let dummy_exp = spanned(
                kind_loc,
                T::Exp_::Value(spanned(kind_loc, T::Value_::Bool(false))),
            );
            let res = |k: T::SpecConditionKind_| {
                Ok(T::SpecBlockMember_::Condition {
                    kind: spanned(kind_loc, k),
                    properties: properties_res,
                    exp: dummy_exp,
                    additional_exps: exps_res,
                })
            };

            match kind.value() {
                P::CommaSpecCondition::AbortsWith => res(T::SpecConditionKind_::AbortsWith),
                P::CommaSpecCondition::Modifies => res(T::SpecConditionKind_::Modifies),
            }
        }
        P::SpecConditionKind_::Emits {
            loc,
            properties,
            exp,
            to_exp,
            if_exp,
        } => {
            let name_loc = loc.loc(&ast.source_tokens);
            let properties_res = properties
                .iter()
                .map(|p| translate_progma_property(ast, p))
                .collect::<Result<Vec<_>, _>>()?;
            let exp_res = translate_exp(context, ast, exp)?;
            let mut additional_exp = vec![];
            let to_exp_res = translate_exp(context, ast, to_exp)?;
            additional_exp.push(to_exp_res);
            match if_exp {
                Some(e) => {
                    let e_res = translate_exp(context, ast, e)?;
                    additional_exp.push(e_res);
                }
                None => (),
            };
            Ok(T::SpecBlockMember_::Condition {
                kind: spanned(name_loc, T::SpecConditionKind_::Emits),
                properties: properties_res,
                exp: exp_res,
                additional_exps: additional_exp,
            })
        }
        P::SpecConditionKind_::Invariant {
            types,
            properties,
            exp,
        } => {
            let leading_comments = cond.leading_comments(&ast.source_tokens);
            let loc = types.loc(&ast.source_tokens);
            context.insert_comments(loc.start(), leading_comments);
            let types = translate_type_parameter(ast, &types.value())?;
            let properties_res = properties
                .iter()
                .map(|p| translate_progma_property(ast, p))
                .collect::<Result<Vec<_>, _>>()?;
            let exp_res = translate_exp(context, ast, exp)?;
            Ok(T::SpecBlockMember_::Condition {
                kind: spanned(loc, T::SpecConditionKind_::Invariant(types)),
                properties: properties_res,
                exp: exp_res,
                additional_exps: vec![],
            })
        }
        P::SpecConditionKind_::InvariantUpdate {
            types,
            properties,
            exp,
        } => {
            let loc = types.loc(&ast.source_tokens);
            let types = translate_type_parameter(ast, &types.value())?;
            let properties_res = properties
                .iter()
                .map(|p| translate_progma_property(ast, p))
                .collect::<Result<Vec<_>, _>>()?;
            let exp_res = translate_exp(context, ast, exp)?;
            Ok(T::SpecBlockMember_::Condition {
                kind: spanned(loc, T::SpecConditionKind_::InvariantUpdate(types)),
                properties: properties_res,
                exp: exp_res,
                additional_exps: vec![],
            })
        }
        P::SpecConditionKind_::Axiom {
            types,
            properties,
            exp,
        } => {
            let loc = types.loc(&ast.source_tokens);
            let types = translate_type_parameter(ast, &types.value())?;
            let properties_res = properties
                .iter()
                .map(|p| translate_progma_property(ast, p))
                .collect::<Result<Vec<_>, _>>()?;
            let exp_res = translate_exp(context, ast, exp)?;
            Ok(T::SpecBlockMember_::Condition {
                kind: spanned(loc, T::SpecConditionKind_::Axiom(types)),
                properties: properties_res,
                exp: exp_res,
                additional_exps: vec![],
            })
        }
    }
}

fn translate_spec_member(
    context: &mut Context,
    ast: &P::PackageDefinition,
    members: &P::SpecBlockMember,
) -> Result<T::SpecBlockMember, Diagnostic> {
    let leading_comments = members.leading_comments(&ast.source_tokens);
    let loc = members.loc(&ast.source_tokens);
    context.insert_comments(loc.start(), leading_comments);

    let member_res = match members.value() {
        P::SpecBlockMember_::Condition(kind) => translate_spec_condition_kind(context, ast, kind),
        P::SpecBlockMember_::Function {
            uninterpreted,
            name,
            signature,
            body,
        } => {
            let func_name = translate_function_name(ast, name)?;
            let signature_res = translate_function_signature(ast, signature, func_name.loc())?;
            let body_res = translate_function_body(context, ast, body)?;
            Ok(T::SpecBlockMember_::Function {
                uninterpreted: *uninterpreted,
                name: func_name,
                signature: signature_res,
                body: body_res,
            })
        }
        P::SpecBlockMember_::Variable {
            is_global,
            name,
            type_parameters,
            type_,
            init,
        } => {
            let name_res = translate_token_to_name(ast, name)?;
            let type_parameter_res = translate_type_parameter(ast, type_parameters)?;
            let type_res = translate_type(ast, type_)?;
            let init_res = match init {
                None => Ok(None),
                Some(i) => Ok(Some(translate_exp(context, ast, i)?)),
            }?;
            Ok(T::SpecBlockMember_::Variable {
                is_global: *is_global,
                name: name_res,
                type_parameters: type_parameter_res,
                type_: type_res,
                init: init_res,
            })
        }
        P::SpecBlockMember_::Let {
            name,
            post_state,
            def,
        } => {
            let name_res = translate_token_to_name(ast, name)?;
            let def_res = translate_exp(context, ast, def)?;
            Ok(T::SpecBlockMember_::Let {
                name: name_res,
                post_state: *post_state,
                def: def_res,
            })
        }
        P::SpecBlockMember_::Update { lhs, rhs } => {
            let lhs_res = translate_exp(context, ast, lhs)?;
            let rhs_res = translate_exp(context, ast, rhs)?;
            Ok(T::SpecBlockMember_::Update {
                lhs: lhs_res,
                rhs: rhs_res,
            })
        }
        P::SpecBlockMember_::Include { properties, exp } => {
            let properties_res = properties
                .iter()
                .map(|p| translate_progma_property(ast, p))
                .collect::<Result<Vec<_>, _>>()?;
            let exp_res = translate_exp(context, ast, exp)?;
            Ok(T::SpecBlockMember_::Include {
                properties: properties_res,
                exp: exp_res,
            })
        }
        P::SpecBlockMember_::Apply {
            exp,
            patterns,
            exclusion_patterns,
        } => {
            let exp_res = translate_exp(context, ast, exp)?;
            let patters_res = patterns
                .iter()
                .map(|p| translate_spec_pattern(ast, p))
                .collect::<Result<Vec<_>, _>>()?;
            let exclusion_patterns_res = exclusion_patterns
                .iter()
                .map(|p| translate_spec_pattern(ast, p))
                .collect::<Result<Vec<_>, _>>()?;

            Ok(T::SpecBlockMember_::Apply {
                exp: exp_res,
                patterns: patters_res,
                exclusion_patterns: exclusion_patterns_res,
            })
        }
        P::SpecBlockMember_::Pragma { properties } => {
            let properties_res = properties
                .iter()
                .map(|p| translate_progma_property(ast, p))
                .collect::<Result<Vec<_>, _>>()?;

            Ok(T::SpecBlockMember_::Pragma {
                properties: properties_res,
            })
        }
    }?;
    Ok(spanned(loc, member_res))
}

fn translate_spec_pattern(
    ast: &P::PackageDefinition,
    pattern: &P::SpecApplyPattern,
) -> Result<T::SpecApplyPattern, Diagnostic> {
    let loc = pattern.loc(&ast.source_tokens);
    let visibility = match &pattern.value().visibility {
        Some(v) => {
            let vis = translate_visibility(ast, &v);
            Ok(Some(vis))
        }
        None => Ok(None),
    }?;
    let name_pattern = pattern
        .value()
        .name_pattern
        .iter()
        .map(|np| translate_spec_apply(ast, np))
        .collect::<Result<Vec<_>, _>>()?;
    let type_parameters = translate_type_parameter(ast, &pattern.value().type_parameters)?;
    Ok(spanned(
        loc,
        T::SpecApplyPattern_ {
            visibility,
            name_pattern,
            type_parameters,
        },
    ))
}

fn translate_spec_apply(
    ast: &P::PackageDefinition,
    apply: &P::SpecApplyFragment,
) -> Result<T::SpecApplyFragment, Diagnostic> {
    let loc = apply.loc(&ast.source_tokens);
    let fragment = match apply.value().kind {
        Tok::Identifier => {
            let name = translate_token_to_name(ast, apply)?;
            Ok(T::SpecApplyFragment_::NamePart(name))
        }
        Tok::Star => Ok(T::SpecApplyFragment_::Wildcard),
        _ => {
            return Err(unexpected_token_error(
                apply.loc(&ast.source_tokens),
                "",
                "a name fragment or `*`",
            ))
        }
    }?;
    Ok(spanned(loc, fragment))
}
fn translate_progma_property(
    ast: &P::PackageDefinition,
    property: &P::PragmaProperty,
) -> Result<T::PragmaProperty, Diagnostic> {
    let loc = property.loc(&ast.source_tokens);
    let property_name = translate_token_to_name(ast, &property.value().name)?;

    let property = match &property.value().value {
        Some(p) => match p {
            P::PragmaValue::Literal(val) => {
                let val_res = translate_value(ast, &val)?;
                Ok(Some(T::PragmaValue::Literal(val_res)))
            }
            P::PragmaValue::Ident(names) => {
                let names_res = translate_name_access_chain(ast, &names)?;
                Ok(Some(T::PragmaValue::Ident(names_res)))
            }
        },
        None => Ok(None),
    }?;
    Ok(spanned(
        loc,
        T::PragmaProperty_ {
            name: property_name,
            value: property,
        },
    ))
}

fn translate_spec_target(
    ast: &P::PackageDefinition,
    spec_target: &P::SpecBlockTarget,
) -> Result<T::SpecBlockTarget, Diagnostic> {
    let loc = spec_target.loc(&ast.source_tokens);
    let target_res = match spec_target.value() {
        P::SpecBlockTarget_::Code => Ok(T::SpecBlockTarget_::Code),
        P::SpecBlockTarget_::Module => Ok(T::SpecBlockTarget_::Module),
        P::SpecBlockTarget_::Member(name, signature_opt) => {
            let name_res = translate_token_to_name(ast, name)?;
            let signature = match signature_opt {
                None => Ok(None),
                Some(sig) => {
                    let sigs = translate_function_signature(ast, sig, name_res.loc)?;
                    Ok(Some(Box::new(sigs)))
                }
            }?;
            Ok(T::SpecBlockTarget_::Member(name_res, signature))
        }
        P::SpecBlockTarget_::Schema(name, type_parameters) => {
            let name_res = translate_token_to_name(ast, name)?;
            let type_parameters_res = translate_type_parameter(ast, type_parameters)?;
            Ok(T::SpecBlockTarget_::Schema(name_res, type_parameters_res))
        }
    }?;
    Ok(spanned(loc, target_res))
}
