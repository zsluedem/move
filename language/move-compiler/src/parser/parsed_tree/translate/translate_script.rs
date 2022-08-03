// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::{
    diag,
    diagnostics::Diagnostic,
    parser::{
        ast::{self as T},
        parsed_tree::ast::{self as P},
    },
};

use super::{
    translate_attribute::tranlsate_vec_attributes, translate_constant::translate_constant,
    translate_function::translate_function, translate_spec::translate_spec_block,
    translate_use::translate_use_decl, Context,
};

pub fn translate_script(
    context: &mut Context,
    ast: &P::PackageDefinition,
    script: &P::Script,
) -> Result<T::Script, Diagnostic> {
    let loc = script.loc(&ast.source_tokens);
    let attributes = tranlsate_vec_attributes(ast, &script.value().attributes)?;
    let mut uses = vec![];
    let mut constants = vec![];
    let mut function = None;
    let mut specs = vec![];
    for member in &script.value().members {
        match member {
            P::ParsedTree::Function(func) => {
                if function.is_none() {
                    function = Some(translate_function(context, ast, &func)?);
                } else {
                    let loc = func.loc(&ast.source_tokens);
                    return Err(diag!(
                        Declarations::InvalidFunction,
                        (loc, "Duplicated function in 'Script'")
                    ));
                }
            }
            P::ParsedTree::Struct(s) => {
                let loc = s.loc(&ast.source_tokens);
                return Err(diag!(
                    Declarations::InvalidStruct,
                    (loc, "Struct is not allowed in 'Script'")
                ));
            }
            P::ParsedTree::Sequence(item) => match item.value() {
                P::SequenceItem_::UseDecl(use_) => {
                    let use_res = translate_use_decl(ast, use_)?;
                    uses.push(use_res)
                }
                P::SequenceItem_::FriendDecl(friend) => {
                    let loc = friend.friend.loc(&ast.source_tokens);
                    return Err(diag!(
                        Declarations::InvalidFriendDeclaration,
                        (loc, "Friend is not allowed in 'Script'")
                    ));
                }
                P::SequenceItem_::Declare(decl) => {
                    let loc = decl.loc(&ast.source_tokens);
                    return Err(diag!(
                        Declarations::InvalidLet,
                        (loc, "Let is not allowed in 'Script'")
                    ));
                }
                P::SequenceItem_::Bind(assign) => {
                    let loc = assign.loc(&ast.source_tokens);
                    return Err(diag!(
                        Declarations::InvalidLet,
                        (loc, "Let is not allowed in 'Script'")
                    ));
                }
                P::SequenceItem_::Constant(constant) => {
                    let constant_res = translate_constant(context, ast, constant)?;
                    constants.push(constant_res)
                }
                P::SequenceItem_::Exp(e, _) => {
                    let loc = e.loc(&ast.source_tokens);
                    return Err(diag!(
                        Declarations::InvalidExpression,
                        (loc, "Expression is not allowed in 'Script'")
                    ));
                }
                P::SequenceItem_::Spec(spec_block) => {
                    let spec_res = translate_spec_block(context, ast, spec_block)?;
                    specs.push(spec_res)
                }
            },
        }
    }
    match function {
        None => Err(diag!(
            Declarations::InvalidScript,
            (loc, "Expected a function in 'Script'")
        )),
        Some(func) => Ok(T::Script {
            attributes,
            loc,
            uses,
            constants,
            function: func,
            specs,
        }),
    }
}
