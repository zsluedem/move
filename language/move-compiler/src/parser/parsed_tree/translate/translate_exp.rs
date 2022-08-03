// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use std::vec;

use move_ir_types::location::Loc;
use move_symbol_pool::Symbol;

use super::{
    spanned, translate_field,
    translate_let::{translate_bind_list, translate_let_assign, translate_let_declare},
    translate_name_access_chain,
    translate_spec::translate_spec_block,
    translate_token_to_name,
    translate_type::{translate_optional_types, translate_type},
    translate_use::translate_use_decl,
    translate_value, translate_var, Context,
};
use crate::{
    diag,
    diagnostics::Diagnostic,
    parser::{
        ast::{self as T},
        parsed_tree::ast::{self as P},
        syntax::make_builtin_call,
    },
};

pub fn translate_exp(
    context: &mut Context,
    ast: &P::PackageDefinition,
    exp: &P::Exp,
) -> Result<T::Exp, Diagnostic> {
    let loc = exp.loc(&ast.source_tokens);
    let exp_ = match exp.value() {
        P::Exp_::Value(val) => Ok(T::Exp_::Value(translate_value(ast, val)?)),
        P::Exp_::Move(var) => Ok(T::Exp_::Move(translate_var(ast, var)?)),
        P::Exp_::Copy(var) => Ok(T::Exp_::Copy(translate_var(ast, var)?)),
        P::Exp_::Name(names, types) => {
            let (names_res, types_res) = translate_exp_name(ast, names, types)?;
            Ok(T::Exp_::Name(names_res, types_res))
        }
        P::Exp_::Call(names, is_macro, type_, e) => {
            let args_loc = e.loc(&ast.source_tokens);
            let (name, type_res, exp_res) =
                translate_exp_call(context, ast, names, type_, e.value())?;
            Ok(T::Exp_::Call(
                name,
                *is_macro,
                type_res,
                spanned(args_loc, exp_res),
            ))
        }
        P::Exp_::Pack(name, types, fields) => translate_exp_pack(context, ast, name, types, fields),
        P::Exp_::Vector(name, type_, contents) => {
            translate_exp_vector(context, ast, name, type_, contents)
        }
        P::Exp_::IfElse(cond, if_statement, else_statement) => {
            translate_exp_if_else(context, ast, cond, if_statement, else_statement)
        }
        P::Exp_::While(cond, body, spec_opt) => {
            translate_exp_while(context, ast, cond, body, spec_opt)
        }
        P::Exp_::Loop(body) => translate_exp_loop(context, ast, body),
        P::Exp_::Block(block) => translate_exp_block(context, ast, block),
        P::Exp_::Lambda(bind_list, body) => {
            let bind_list_res = translate_bind_list(ast, bind_list)?;
            let body_res = translate_exp(context, ast, body)?;
            Ok(T::Exp_::Lambda(bind_list_res, Box::new(body_res)))
        }
        P::Exp_::Quant(kind, binds, exps, where_cond, exp) => {
            translate_quant(context, ast, kind, binds, exps, where_cond, exp)
        }
        P::Exp_::ExpList(exps) => {
            let exps_res = exps
                .iter()
                .map(|e| translate_exp(context, ast, e))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(T::Exp_::ExpList(exps_res))
        }
        P::Exp_::Unit => Ok(T::Exp_::Unit),
        P::Exp_::Assign(var, body) => {
            let var_res = translate_exp(context, ast, var)?;
            let body_res = translate_exp(context, ast, body)?;
            Ok(T::Exp_::Assign(Box::new(var_res), Box::new(body_res)))
        }
        P::Exp_::Return(exp_opt) => match exp_opt {
            Some(exp) => {
                let exp_res = translate_exp(context, ast, exp)?;
                Ok(T::Exp_::Return(Some(Box::new(exp_res))))
            }
            _ => Ok(T::Exp_::Return(None)),
        },
        P::Exp_::Abort(e) => {
            let exp_res = translate_exp(context, ast, e)?;
            Ok(T::Exp_::Abort(Box::new(exp_res)))
        }
        P::Exp_::Break => Ok(T::Exp_::Break),
        P::Exp_::Continue => Ok(T::Exp_::Continue),
        P::Exp_::UnaryExp(op, e) => translate_unary_exp(context, ast, op, e),
        P::Exp_::BinopExp(lhs, op, rhs) => translate_binop_exp(context, ast, op, lhs, rhs),
        P::Exp_::Dot(e, name) => {
            let exp_res = translate_exp(context, ast, e)?;
            let name = translate_token_to_name(ast, name)?;
            Ok(T::Exp_::Dot(Box::new(exp_res), name))
        }
        P::Exp_::Index(e, exp_in) => {
            let exp_res = translate_exp(context, ast, e)?;
            let exp_in_res = translate_exp(context, ast, exp_in)?;
            Ok(T::Exp_::Index(Box::new(exp_res), Box::new(exp_in_res)))
        }
        P::Exp_::Cast(e, type_) => {
            let exp_res = translate_exp(context, ast, e)?;
            let type_res = translate_type(ast, type_)?;
            Ok(T::Exp_::Cast(Box::new(exp_res), type_res))
        }
        P::Exp_::Annotate(e, type_) => {
            let exp_res = translate_exp(context, ast, e)?;
            let type_res = translate_type(ast, type_)?;
            Ok(T::Exp_::Annotate(Box::new(exp_res), type_res))
        }
        P::Exp_::UnresolvedError => Ok(T::Exp_::UnresolvedError),
    }?;

    Ok(spanned(loc, exp_))
}

fn translate_quant(
    context: &mut Context,
    ast: &P::PackageDefinition,
    quant: &P::QuantKind,
    binds: &P::BindWithRangeList,
    exps: &[Vec<P::Exp>],
    where_cond: &Option<Box<P::Exp>>,
    exp: &P::Exp,
) -> Result<T::Exp_, Diagnostic> {
    let kind = translate_quant_kind(ast, quant)?;
    let binds_res = transalte_quant_bind_list(context, ast, binds)?;
    let exps_res = exps
        .iter()
        .map(|exps_| {
            exps_
                .iter()
                .map(|e| translate_exp(context, ast, e))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;
    let where_cond_res = match where_cond {
        Some(e) => Ok(Some(Box::new(translate_exp(context, ast, &e)?))),
        None => Ok(None),
    }?;
    let exp_res = translate_exp(context, ast, &exp)?;
    Ok(T::Exp_::Quant(
        kind,
        binds_res,
        exps_res,
        where_cond_res,
        Box::new(exp_res),
    ))
}

fn transalte_quant_bind_list(
    context: &mut Context,
    ast: &P::PackageDefinition,
    binds: &P::BindWithRangeList,
) -> Result<T::BindWithRangeList, Diagnostic> {
    let loc = binds.loc(&ast.source_tokens);
    let res = binds
        .value()
        .iter()
        .map(|b| {
            let loc = b.loc(&ast.source_tokens);
            match b.value() {
                P::QuantBind::TypeBind(var, type_) => {
                    let var_res = T::Bind_::Var(translate_var(ast, var)?);
                    let bind_res = spanned(var.loc(&ast.source_tokens), var_res);
                    let type_res = translate_type(ast, type_)?;
                    let exp = make_builtin_call(
                        type_res.loc,
                        Symbol::from("$spec_domain"),
                        Some(vec![type_res]),
                        vec![],
                    );
                    Ok(spanned(loc, (bind_res, exp)))
                }
                P::QuantBind::InBind(var, exp) => {
                    let var_res = T::Bind_::Var(translate_var(ast, var)?);
                    let bind_res = spanned(var.loc(&ast.source_tokens), var_res);
                    let exp_res = translate_exp(context, ast, exp)?;
                    Ok(spanned(loc, (bind_res, exp_res)))
                }
            }
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(spanned(loc, res))
}

fn translate_quant_kind(
    ast: &P::PackageDefinition,
    quant_kind: &P::QuantKind,
) -> Result<T::QuantKind, Diagnostic> {
    let loc = quant_kind.loc(&ast.source_tokens);
    let kind = quant_kind.value;
    Ok(spanned(loc, kind))
}

fn translate_binop_exp(
    context: &mut Context,
    ast: &P::PackageDefinition,
    op: &P::BinOp,
    lhs: &P::Exp,
    rhs: &P::Exp,
) -> Result<T::Exp_, Diagnostic> {
    let lhs_res = translate_exp(context, ast, lhs)?;
    let rhs_res = translate_exp(context, ast, rhs)?;
    let op_loc = op.loc(&ast.source_tokens);

    Ok(T::Exp_::BinopExp(
        Box::new(lhs_res),
        spanned(op_loc, op.value),
        Box::new(rhs_res),
    ))
}

fn translate_unary_exp(
    context: &mut Context,
    ast: &P::PackageDefinition,
    op: &P::UnaryOp,
    exp: &P::Exp,
) -> Result<T::Exp_, Diagnostic> {
    let exp_res = translate_exp(context, ast, exp)?;
    let op_loc = op.loc(&ast.source_tokens);
    match op.value() {
        P::UnaryOp_::Not => Ok(T::Exp_::UnaryExp(
            spanned(op_loc, T::UnaryOp_::Not),
            Box::new(exp_res),
        )),
        P::UnaryOp_::Borrow => Ok(T::Exp_::Borrow(false, Box::new(exp_res))),
        P::UnaryOp_::BorrowMut => Ok(T::Exp_::Borrow(true, Box::new(exp_res))),
        P::UnaryOp_::Dereference => Ok(T::Exp_::Dereference(Box::new(exp_res))),
    }
}

pub fn translate_exp_block(
    context: &mut Context,
    ast: &P::PackageDefinition,
    block: &P::Block,
) -> Result<T::Exp_, Diagnostic> {
    let res = translate_exp_sequence(context, ast, block)?;
    Ok(T::Exp_::Block(res))
}

pub fn translate_exp_sequence(
    context: &mut Context,
    ast: &P::PackageDefinition,
    block: &P::Block,
) -> Result<T::Sequence, Diagnostic> {
    let mut uses = vec![];
    let mut sequences = vec![];
    let mut end_semicolon: Option<Loc> = None;
    let mut end_exp: Option<T::Exp> = None;
    for item in block {
        match item.value() {
            P::SequenceItem_::UseDecl(use_decl) => {
                // there are no attributes before use in original syntax
                let use_res = translate_use_decl(ast, use_decl)?;
                uses.push(use_res);
            }
            P::SequenceItem_::FriendDecl(f) => {
                let loc = f.friend.loc(&ast.source_tokens);
                return Err(diag!(Declarations::InvalidFriendDeclaration, (loc, "")));
            }
            P::SequenceItem_::Declare(decl) => {
                let loc = item.loc(&ast.source_tokens);
                let decl = translate_let_declare(ast, decl)?;
                let item_res = spanned(loc, decl);
                sequences.push(item_res);
            }
            P::SequenceItem_::Bind(assign) => {
                let loc = assign.loc(&ast.source_tokens);
                let assign_res = translate_let_assign(context, ast, assign)?;
                let item_res = spanned(loc, assign_res);
                sequences.push(item_res);
            }
            P::SequenceItem_::Constant(constant) => {
                let loc = constant.constant.loc(&ast.source_tokens);
                return Err(diag!(Declarations::InvalidConstant, (loc, "")));
            }
            P::SequenceItem_::Exp(exp, is_semi_colon_end) => {
                let exp_ = translate_exp(context, ast, exp)?;
                match is_semi_colon_end {
                    P::SemicolonEnd::IsSemicolonEnd(token) => match end_exp {
                        Some(end_exp_) => {
                            return Err(diag!(
                                Declarations::InvalidExpression,
                                (end_exp_.loc, "expected ';' in the end")
                            ))
                        }
                        None => {
                            end_exp = Some(exp_);
                            end_semicolon = Some(token.loc);
                        }
                    },
                    P::SemicolonEnd::NotSemicolonEnd => {
                        let loc = item.loc(&ast.source_tokens);
                        let item_res = spanned(loc, T::SequenceItem_::Seq(Box::new(exp_)));
                        sequences.push(item_res);
                    }
                }
            }
            P::SequenceItem_::Spec(spec_block) => {
                let spec = translate_spec_block(context, ast, spec_block)?;
                let loc = item.loc(&ast.source_tokens);
                let item_res = spanned(
                    loc,
                    T::SequenceItem_::Seq(Box::new(spanned(loc, T::Exp_::Spec(spec)))),
                );
                sequences.push(item_res)
            }
        }
    }
    Ok((uses, sequences, end_semicolon, Box::new(end_exp)))
}

fn translate_exp_loop(
    context: &mut Context,
    ast: &P::PackageDefinition,
    body: &P::Exp,
) -> Result<T::Exp_, Diagnostic> {
    let body_res = translate_exp(context, ast, body)?;
    Ok(T::Exp_::Loop(Box::new(body_res)))
}

fn translate_exp_while(
    context: &mut Context,
    ast: &P::PackageDefinition,
    cond: &P::Exp,
    body: &P::Exp,
    spec_opt: &Option<P::SpecBlock>,
) -> Result<T::Exp_, Diagnostic> {
    let cond_res = translate_exp(context, ast, &cond)?;
    let loop_res = translate_exp(context, ast, &body)?;
    let econd = match spec_opt {
        Some(spec) => {
            for member in &spec.value().members {
                match member.value() {
                    P::SpecBlockMember_::Condition(..) => {}
                    _ => {
                        return Err(diag!(
                            Syntax::InvalidSpecBlockMember,
                            (
                                member.loc(&ast.source_tokens),
                                "only 'invariant' allowed here"
                            )
                        ))
                    }
                }
            }
            let spec_loc = spec.loc(&ast.source_tokens);
            let spec_res = translate_spec_block(context, ast, spec)?;
            Ok(spanned(
                cond_res.loc,
                T::Exp_::Block((
                    vec![],
                    vec![spanned(
                        spec_loc,
                        T::SequenceItem_::Seq(Box::new(spanned(spec_loc, T::Exp_::Spec(spec_res)))),
                    )],
                    None,
                    Box::new(Some(cond_res)),
                )),
            ))
        }
        None => Ok(cond_res),
    }?;

    Ok(T::Exp_::While(Box::new(econd), Box::new(loop_res)))
}

fn translate_exp_if_else(
    context: &mut Context,
    ast: &P::PackageDefinition,
    cond: &P::Exp,
    if_statement: &P::Exp,
    else_statement: &Option<Box<P::Exp>>,
) -> Result<T::Exp_, Diagnostic> {
    let cond_res = translate_exp(context, ast, &cond)?;
    let if_statement_res = translate_exp(context, ast, &if_statement)?;
    let else_statement_res = match else_statement {
        Some(el) => Some(Box::new(translate_exp(context, ast, &el)?)),
        None => None,
    };
    Ok(T::Exp_::IfElse(
        Box::new(cond_res),
        Box::new(if_statement_res),
        else_statement_res,
    ))
}

fn translate_exp_vector(
    context: &mut Context,
    ast: &P::PackageDefinition,
    name: &P::Name,
    type_: &Option<Vec<P::Type>>,
    contents: &P::SpannedWithComment<Vec<P::Exp>>,
) -> Result<T::Exp_, Diagnostic> {
    let name_loc = name.loc(&ast.source_tokens);
    let type_res = translate_optional_types(ast, type_)?;
    let content_loc = contents.loc(&ast.source_tokens);
    let content_res = contents
        .value()
        .iter()
        .map(|e| translate_exp(context, ast, e))
        .collect::<Result<Vec<_>, _>>()?;

    Ok(T::Exp_::Vector(
        name_loc,
        type_res,
        spanned(content_loc, content_res),
    ))
}

fn translate_exp_pack(
    context: &mut Context,
    ast: &P::PackageDefinition,
    leading: &P::NameAccessChain,
    type_: &Option<Vec<P::Type>>,
    fields: &[(P::Field, Option<P::Exp>)],
) -> Result<T::Exp_, Diagnostic> {
    let leading_name = translate_name_access_chain(ast, leading)?;
    let type_res = translate_optional_types(ast, type_)?;
    let fields_res = fields
        .iter()
        .map(|(f, e)| {
            let field_res = translate_field(ast, f)?;
            let exp_res = match e {
                Some(exp_) => translate_exp(context, ast, exp_)?,
                // field only situation
                None => {
                    let f_loc = field_res.0.loc;
                    spanned(
                        f_loc,
                        T::Exp_::Name(spanned(f_loc, T::NameAccessChain_::One(field_res.0)), None),
                    )
                }
            };
            Ok((field_res, exp_res))
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(T::Exp_::Pack(leading_name, type_res, fields_res))
}

fn translate_exp_call(
    context: &mut Context,
    ast: &P::PackageDefinition,
    leading: &P::NameAccessChain,
    type_: &Option<Vec<P::Type>>,
    args: &[P::Exp],
) -> Result<(T::NameAccessChain, Option<Vec<T::Type>>, Vec<T::Exp>), Diagnostic> {
    let leading_name = translate_name_access_chain(ast, leading)?;
    let type_res = translate_optional_types(ast, type_)?;

    let exp_res = args
        .iter()
        .map(|exp_| translate_exp(context, ast, exp_))
        .collect::<Result<Vec<_>, _>>()?;
    Ok((leading_name, type_res, exp_res))
}

fn translate_exp_name(
    ast: &P::PackageDefinition,
    leading: &P::NameAccessChain,
    type_: &Option<Vec<P::Type>>,
) -> Result<(T::NameAccessChain, Option<Vec<T::Type>>), Diagnostic> {
    let leading_name = translate_name_access_chain(ast, leading)?;
    let type_res = translate_optional_types(ast, type_)?;
    Ok((leading_name, type_res))
}
