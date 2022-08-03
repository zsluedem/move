// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::{
    diagnostics::Diagnostic,
    parser::{
        lexer::Tok,
        parsed_tree::ast::{
            Attributes, CommaSpecCondition, FunctionBody, FunctionBody_, FunctionSignature,
            ParsedToken, PragmaProperty, PragmaProperty_, PragmaValue, SingleSpecCondition,
            SpannedWithComment, SpecApplyFragment, SpecApplyPattern, SpecApplyPattern_, SpecBlock,
            SpecBlockMember, SpecBlockMember_, SpecBlockTarget, SpecBlockTarget_, SpecBlock_,
            SpecConditionKind, SpecConditionKind_, Type, Var, Visibility, Visibility_,
        },
    },
};

use super::{
    parse_attributes::parse_attributes_vec,
    parse_comma_list, parse_comma_list_after_start,
    parse_exp::{parse_exp, parse_sequence_block, parse_unary_exp},
    parse_identifier::{consume_identifier, match_identifier, parse_identifier},
    parse_list, parse_name_access_chain,
    parse_type::{parse_optional_type_parameters, parse_type},
    parse_use::parse_use_decl,
    parse_value, parse_var, Context,
};

// Parse an optional specification block:
//     SpecBlockTarget =
//          <Identifier>
//        |  "fun" <Identifier>  # deprecated
//        | "struct <Identifier> # deprecated
//        | "module"
//        | "schema" <Identifier> <OptionalTypeParameters>
//        | <empty>
//     SpecBlock =
//        <DocComments> "spec" ( <SpecFunction> | <SpecBlockTarget> "{" SpecBlockMember* "}" )
pub fn parse_spec_block(
    context: &mut Context,
    attributes: Vec<Attributes>,
) -> Result<SpecBlock, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    context.tokens.consume_token(Tok::Spec)?;
    let target_ = match context.tokens.peek() {
        Tok::Fun => {
            return Err(context
                .tokens
                .unexpected_token_error("only 'spec', drop the 'fun' keyword"));
        }
        Tok::Struct => {
            return Err(context
                .tokens
                .unexpected_token_error("only 'spec', drop the 'struct' keyword"));
        }
        Tok::Module => {
            context.tokens.advance()?;
            SpecBlockTarget_::Module
        }
        Tok::Identifier if context.tokens.content() == "schema" => {
            context.tokens.advance()?;
            let name = parse_identifier(context)?;
            let type_parameters = parse_optional_type_parameters(context)?;
            SpecBlockTarget_::Schema(name, type_parameters)
        }
        Tok::Identifier => {
            let name = parse_identifier(context)?;
            let signature = parse_spec_target_signature_opt(context)?;
            SpecBlockTarget_::Member(name, signature)
        }
        Tok::LBrace => SpecBlockTarget_::Code,
        _ => {
            return Err(context
                .tokens
                .unexpected_token_error("one of `module`, `struct`, `fun`, `schema`, or `{`"));
        }
    };
    let target_end_loc = context.tokens.tokens_loc();
    let target = SpecBlockTarget::new(
        target_,
        context.tokens.token_range(start_loc, target_end_loc),
    );

    context.tokens.consume_token(Tok::LBrace)?;
    let mut uses = vec![];
    while context.tokens.peek() == Tok::NumSign || context.tokens.peek() == Tok::Use {
        let attrs = parse_attributes_vec(context)?;
        uses.push(parse_use_decl(context, attrs)?);
    }
    let mut members = vec![];
    while context.tokens.peek() != Tok::RBrace {
        members.push(parse_spec_block_member(context)?);
    }
    context.tokens.consume_token(Tok::RBrace)?;
    let end_loc = context.tokens.tokens_loc();
    let spec = SpecBlock_ {
        attributes,
        target,
        uses,
        members,
    };
    Ok(SpecBlock::new(
        spec,
        context.tokens.token_range(start_loc, end_loc),
    ))
}

// Parse a spec block member:
//    SpecBlockMember = <DocComments> ( <Invariant> | <Condition> | <SpecFunction> | <SpecVariable>
//                                   | <SpecInclude> | <SpecApply> | <SpecPragma> | <SpecLet>
//                                   | <SpecUpdate> | <SpecAxiom> )
fn parse_spec_block_member(context: &mut Context) -> Result<SpecBlockMember, Diagnostic> {
    match context.tokens.peek() {
        Tok::Invariant => parse_invariant(context),
        Tok::Let => parse_spec_let(context),
        Tok::Fun | Tok::Native => parse_spec_function(context),
        Tok::Identifier => match context.tokens.content() {
            "assert" | "assume" | "decreases" | "aborts_if" | "aborts_with" | "succeeds_if"
            | "modifies" | "emits" | "ensures" | "requires" => parse_condition(context),
            "axiom" => parse_axiom(context),
            "include" => parse_spec_include(context),
            "apply" => parse_spec_apply(context),
            "pragma" => parse_spec_pragma(context),
            "global" | "local" => parse_spec_variable(context),
            "update" => parse_spec_update(context),
            _ => {
                // local is optional but supported to be able to declare variables which are
                // named like the weak keywords above
                parse_spec_variable(context)
            }
        },
        _ => Err(context.tokens.unexpected_token_error(
            "one of `assert`, `assume`, `decreases`, `aborts_if`, `aborts_with`, `succeeds_if`, \
             `modifies`, `emits`, `ensures`, `requires`, `include`, `apply`, `pragma`, `global`, \
             or a name",
        )),
    }
}

// Parse an invariant:
//     Invariant = "invariant" <OptionalTypeParameters> [ "update" ] <ConditionProperties> <Exp> ";"
fn parse_invariant(context: &mut Context) -> Result<SpecBlockMember, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    context.tokens.consume_token(Tok::Invariant)?;
    let types = parse_optional_type_parameters(context)?;
    let type_end_loc = context.tokens.tokens_loc();
    let is_update = match context.tokens.peek() {
        Tok::Identifier if context.tokens.content() == "update" => {
            context.tokens.advance()?;
            true
        }
        _ => false,
    };

    let properties = parse_condition_properties(context)?;
    let exp = parse_exp(context)?;
    context.tokens.consume_token(Tok::Semicolon)?;
    let end_loc = context.tokens.tokens_loc();
    let token_range = context.tokens.token_range(start_loc, end_loc);
    let kind = if is_update {
        SpecConditionKind::new(
            SpecConditionKind_::Invariant {
                types: SpannedWithComment {
                    value: types,
                    token_range: context.tokens.token_range(start_loc, type_end_loc),
                },
                properties,
                exp: Box::new(exp),
            },
            token_range,
        )
    } else {
        SpecConditionKind::new(
            SpecConditionKind_::InvariantUpdate {
                types: SpannedWithComment {
                    value: types,
                    token_range: context.tokens.token_range(start_loc, type_end_loc),
                },
                properties,
                exp: Box::new(exp),
            },
            token_range,
        )
    };
    Ok(SpecBlockMember::new(
        SpecBlockMember_::Condition(Box::new(kind)),
        token_range,
    ))
}

// Parse a specification let.
//     SpecLet =  "let" [ "post" ] <Identifier> "=" <Exp> ";"
fn parse_spec_let(context: &mut Context) -> Result<SpecBlockMember, Diagnostic> {
    let start_loc = context.tokens.start_loc();
    context.tokens.advance()?;
    let post_state =
        if context.tokens.peek() == Tok::Identifier && context.tokens.content() == "post" {
            context.tokens.advance()?;
            true
        } else {
            false
        };
    let name = parse_identifier(context)?;
    context.tokens.consume_token(Tok::Equal)?;
    let def = parse_exp(context)?;
    context.tokens.consume_token(Tok::Semicolon)?;
    let end_loc = context.tokens.start_loc();
    Ok(SpecBlockMember::new(
        SpecBlockMember_::Let {
            name,
            post_state,
            def,
        },
        context.tokens.token_range(start_loc, end_loc),
    ))
}

// Parse a specification function.
//     SpecFunction = "define" <SpecFunctionSignature> ( "{" <Sequence> "}" | ";" )
//                  | "native" "define" <SpecFunctionSignature> ";"
//     SpecFunctionSignature =
//         <Identifier> <OptionalTypeParameters> "(" Comma<Parameter> ")" ":" <Type>
fn parse_spec_function(context: &mut Context) -> Result<SpecBlockMember, Diagnostic> {
    let start_loc = context.tokens.start_loc();
    let native_opt = consume_optional_token_with_loc(context, Tok::Native)?;
    context.tokens.consume_token(Tok::Fun)?;
    let name = parse_identifier(context)?;
    let type_parameters = parse_optional_type_parameters(context)?;
    // "(" Comma<Parameter> ")"
    let parameters = parse_comma_list(
        context,
        Tok::LParen,
        Tok::RParen,
        parse_parameter,
        "a function parameter",
    )?;

    // ":" <Type>)
    context.tokens.consume_token(Tok::Colon)?;
    let return_type = parse_type(context)?;

    let body_start_loc = context.tokens.tokens_loc();
    let no_body = context.tokens.peek() != Tok::LBrace;
    let (is_native, body_) = if native_opt.is_some() || no_body {
        context.tokens.consume_token(Tok::Semicolon)?;
        (
            native_opt.is_none(),
            FunctionBody_ {
                body: vec![],
                is_native: native_opt.is_none(),
            },
        )
    } else {
        let seq = parse_sequence_block(context)?;
        (
            false,
            FunctionBody_ {
                body: seq,
                is_native: false,
            },
        )
    };
    let body_end_loc = context.tokens.tokens_loc();
    let body = FunctionBody::new(
        body_,
        context.tokens.token_range(body_start_loc, body_end_loc),
    );

    let signature = FunctionSignature {
        type_parameters,
        parameters,
        return_type: Some(return_type),
    };

    let end_loc = context.tokens.tokens_loc();
    Ok(SpecBlockMember::new(
        SpecBlockMember_::Function {
            uninterpreted: is_native,
            name,
            signature,
            body,
        },
        context.tokens.token_range(start_loc, end_loc),
    ))
}

fn parse_single_condition(
    context: &mut Context,
    kind: SingleSpecCondition,
) -> Result<SpecBlockMember, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    context.tokens.advance()?;
    let name_end_loc = context.tokens.tokens_loc();
    let properties = parse_condition_properties(context)?;
    let exp = parse_exp(context)?;
    context.tokens.consume_token(Tok::Semicolon)?;
    let end_loc = context.tokens.tokens_loc();
    let token_range = context.tokens.token_range(start_loc, end_loc);
    let con = SpecConditionKind::new(
        SpecConditionKind_::SingleExpCondition {
            kind: SpannedWithComment {
                value: kind,
                token_range: context.tokens.token_range(start_loc, name_end_loc),
            },
            properties,
            exp: Box::new(exp),
        },
        token_range,
    );
    Ok(SpecBlockMember::new(
        SpecBlockMember_::Condition(Box::new(con)),
        token_range,
    ))
}

fn parse_comma_spec_condition(
    context: &mut Context,
    kind: CommaSpecCondition,
) -> Result<SpecBlockMember, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    let name_end_loc = context.tokens.tokens_loc();
    let properties = parse_condition_properties(context)?;
    let exps = parse_comma_list_after_start(
        context,
        context.tokens.start_loc(),
        context.tokens.peek(),
        Tok::Semicolon,
        parse_exp,
        "an aborts code or modifies target",
    )?;
    context.tokens.consume_token(Tok::Semicolon)?;
    let end_loc = context.tokens.tokens_loc();
    let token_range = context.tokens.token_range(start_loc, end_loc);
    let con = SpecConditionKind::new(
        SpecConditionKind_::CommaExpCondition {
            kind: SpannedWithComment {
                value: kind,
                token_range: context.tokens.token_range(start_loc, name_end_loc),
            },
            properties,
            exps,
        },
        token_range,
    );

    Ok(SpecBlockMember::new(
        SpecBlockMember_::Condition(Box::new(con)),
        token_range,
    ))
}

// Parse a specification condition:
//    SpecCondition =
//        ("assert" | "assume" | "ensures" | "requires" | "decreases"| "succeeds_if" ) <ConditionProperties> <Exp> ";"
//      | "aborts_if" <ConditionProperties> <Exp> ["with" <Exp>] ";"
//      | "aborts_with" <ConditionProperties> <Exp> [Comma <Exp>]* ";"
//      | "emits" <ConditionProperties> <Exp> "to" <Exp> [If <Exp>] ";"
fn parse_condition(context: &mut Context) -> Result<SpecBlockMember, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    match context.tokens.content() {
        "assert" => parse_single_condition(context, SingleSpecCondition::Assert),
        "assume" => parse_single_condition(context, SingleSpecCondition::Assume),
        "ensures" => parse_single_condition(context, SingleSpecCondition::Ensures),
        "requires" => parse_single_condition(context, SingleSpecCondition::Requires),
        "decreases" => parse_single_condition(context, SingleSpecCondition::Decreases),
        "succeeds_if" => parse_single_condition(context, SingleSpecCondition::SucceedsIf),
        "aborts_if" => {
            let loc = context.tokens.advance()?;
            let properties = parse_condition_properties(context)?;
            let exp = parse_exp(context)?;
            let with_exp = if match_identifier(context, "with")? {
                Some(Box::new(parse_exp(context)?))
            } else {
                None
            };
            context.tokens.consume_token(Tok::Semicolon)?;
            let end_loc = context.tokens.tokens_loc();
            let token_range = context.tokens.token_range(start_loc, end_loc);
            let con = SpecConditionKind::new(
                SpecConditionKind_::AbortsIf {
                    loc,
                    properties,
                    exp: Box::new(exp),
                    with_exp,
                },
                token_range,
            );
            Ok(SpecBlockMember::new(
                SpecBlockMember_::Condition(Box::new(con)),
                token_range,
            ))
        }
        "aborts_with" => parse_comma_spec_condition(context, CommaSpecCondition::AbortsWith),
        "modifies" => parse_comma_spec_condition(context, CommaSpecCondition::Modifies),
        "emits" => {
            let loc = context.tokens.advance()?;
            let properties = parse_condition_properties(context)?;
            let exp = parse_exp(context)?;
            consume_identifier(context, "to")?;
            let to_exp = parse_exp(context)?;
            let if_exp = if context.tokens.match_token(Tok::If)? {
                Some(Box::new(parse_exp(context)?))
            } else {
                None
            };
            context.tokens.consume_token(Tok::Semicolon)?;
            let end_loc = context.tokens.tokens_loc();
            let token_range = context.tokens.token_range(start_loc, end_loc);
            let con = SpecConditionKind::new(
                SpecConditionKind_::Emits {
                    loc,
                    properties,
                    exp: Box::new(exp),
                    to_exp: Box::new(to_exp),
                    if_exp,
                },
                token_range,
            );

            Ok(SpecBlockMember::new(
                SpecBlockMember_::Condition(Box::new(con)),
                token_range,
            ))
        }
        _ => unreachable!(),
    }
}

// Parse an axiom:
//     a = "axiom" <OptionalTypeParameters> <ConditionProperties> <Exp> ";"
fn parse_axiom(context: &mut Context) -> Result<SpecBlockMember, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    consume_identifier(context, "axiom")?;
    let types = parse_optional_type_parameters(context)?;
    let type_end_loc = context.tokens.tokens_loc();

    let properties = parse_condition_properties(context)?;
    let exp = parse_exp(context)?;
    context.tokens.consume_token(Tok::Semicolon)?;
    let end_loc = context.tokens.tokens_loc();
    let token_range = context.tokens.token_range(start_loc, end_loc);
    let con = SpecConditionKind::new(
        SpecConditionKind_::Axiom {
            types: SpannedWithComment {
                value: types,
                token_range: context.tokens.token_range(start_loc, type_end_loc),
            },
            properties,
            exp: Box::new(exp),
        },
        token_range,
    );

    Ok(SpecBlockMember::new(
        SpecBlockMember_::Condition(Box::new(con)),
        token_range,
    ))
}
// Parse a specification schema include.
//    SpecInclude = "include" <Exp>
fn parse_spec_include(context: &mut Context) -> Result<SpecBlockMember, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    consume_identifier(context, "include")?;
    let properties = parse_condition_properties(context)?;
    let exp = parse_exp(context)?;
    context.tokens.consume_token(Tok::Semicolon)?;
    let end_loc = context.tokens.tokens_loc();
    let token_range = context.tokens.token_range(start_loc, end_loc);
    Ok(SpecBlockMember::new(
        SpecBlockMember_::Include { properties, exp },
        token_range,
    ))
}

// Parse a specification schema apply.
//    SpecApply = "apply" <Exp> "to" Comma<SpecApplyPattern>
//                                   ( "except" Comma<SpecApplyPattern> )? ";"
fn parse_spec_apply(context: &mut Context) -> Result<SpecBlockMember, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    consume_identifier(context, "apply")?;
    let exp = parse_exp(context)?;
    consume_identifier(context, "to")?;
    let parse_patterns = |context: &mut Context| {
        parse_list(
            context,
            |context| {
                if context.tokens.peek() == Tok::Comma {
                    context.tokens.advance()?;
                    Ok(true)
                } else {
                    Ok(false)
                }
            },
            parse_spec_apply_pattern,
        )
    };
    let patterns = parse_patterns(context)?;
    let exclusion_patterns =
        if context.tokens.peek() == Tok::Identifier && context.tokens.content() == "except" {
            context.tokens.advance()?;
            parse_patterns(context)?
        } else {
            vec![]
        };
    context.tokens.consume_token(Tok::Semicolon)?;
    let end_loc = context.tokens.tokens_loc();
    let value = SpecBlockMember_::Apply {
        exp,
        patterns,
        exclusion_patterns,
    };
    Ok(SpecBlockMember::new(
        value,
        context.tokens.token_range(start_loc, end_loc),
    ))
}

// Parse a specification pragma:
//    SpecPragma = "pragma" Comma<SpecPragmaProperty> ";"
fn parse_spec_pragma(context: &mut Context) -> Result<SpecBlockMember, Diagnostic> {
    let start_loc = context.tokens.start_loc();
    consume_identifier(context, "pragma")?;
    let properties = parse_comma_list_after_start(
        context,
        start_loc,
        Tok::Identifier,
        Tok::Semicolon,
        parse_spec_property,
        "a pragma property",
    )?;
    let end_loc = context.tokens.tokens_loc();
    let spec = SpecBlockMember_::Pragma { properties };
    Ok(SpecBlockMember::new(
        spec,
        context.tokens.token_range(start_loc, end_loc),
    ))
}

// Parse a specification variable.
//     SpecVariable = ( "global" | "local" )?
//                    <Identifier> <OptionalTypeParameters>
//                    ":" <Type>
//                    [ "=" Exp ]  // global only
//                    ";"
fn parse_spec_variable(context: &mut Context) -> Result<SpecBlockMember, Diagnostic> {
    let start_loc = context.tokens.start_loc();
    let is_global = match context.tokens.content() {
        "global" => {
            context.tokens.consume_token(Tok::Identifier)?;
            true
        }
        "local" => {
            context.tokens.consume_token(Tok::Identifier)?;
            false
        }
        _ => false,
    };
    let name = parse_identifier(context)?;
    let type_parameters = parse_optional_type_parameters(context)?;
    context.tokens.consume_token(Tok::Colon)?;
    let type_ = parse_type(context)?;
    let init = if is_global && context.tokens.peek() == Tok::Equal {
        context.tokens.advance()?;
        Some(parse_exp(context)?)
    } else {
        None
    };

    context.tokens.consume_token(Tok::Semicolon)?;
    let end_loc = context.tokens.tokens_loc();
    let spec = SpecBlockMember_::Variable {
        is_global,
        name,
        type_parameters,
        type_,
        init,
    };
    Ok(SpecBlockMember::new(
        spec,
        context.tokens.token_range(start_loc, end_loc),
    ))
}
// Parse a specification update.
//     SpecUpdate = "update" <Exp> = <Exp> ";"
fn parse_spec_update(context: &mut Context) -> Result<SpecBlockMember, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    context.tokens.consume_token(Tok::Identifier)?;
    let lhs = parse_unary_exp(context)?;
    context.tokens.consume_token(Tok::Equal)?;
    let rhs = parse_exp(context)?;
    context.tokens.consume_token(Tok::Semicolon)?;
    let end_loc = context.tokens.tokens_loc();
    let spec = SpecBlockMember_::Update { lhs, rhs };
    Ok(SpecBlockMember::new(
        spec,
        context.tokens.token_range(start_loc, end_loc),
    ))
}

fn parse_spec_target_signature_opt(
    context: &mut Context,
) -> Result<Option<Box<FunctionSignature>>, Diagnostic> {
    match context.tokens.peek() {
        Tok::Less | Tok::LParen => {
            let type_parameters = parse_optional_type_parameters(context)?;
            // "(" Comma<Parameter> ")"
            let parameters = parse_comma_list(
                context,
                Tok::LParen,
                Tok::RParen,
                parse_parameter,
                "a function parameter",
            )?;
            // (":" <Type>)?
            let return_type = if context.tokens.match_token(Tok::Colon)? {
                Some(parse_type(context)?)
            } else {
                None
            };
            Ok(Some(Box::new(FunctionSignature {
                type_parameters,
                parameters,
                return_type,
            })))
        }
        _ => Ok(None),
    }
}

// Parse properties in a condition.
//   ConditionProperties = ( "[" Comma<SpecPragmaProperty> "]" )?
fn parse_condition_properties(context: &mut Context) -> Result<Vec<PragmaProperty>, Diagnostic> {
    let properties = if context.tokens.peek() == Tok::LBracket {
        parse_comma_list(
            context,
            Tok::LBracket,
            Tok::RBracket,
            parse_spec_property,
            "a condition property",
        )?
    } else {
        vec![]
    };
    Ok(properties)
}

// Parse a specification pragma property:
//    SpecPragmaProperty = <Identifier> ( "=" <Value> | <NameAccessChain> )?
fn parse_spec_property(context: &mut Context) -> Result<PragmaProperty, Diagnostic> {
    let start_loc = context.tokens.start_loc();
    let name = match consume_optional_token_with_loc(context, Tok::Friend)? {
        // special treatment for `pragma friend = ...` as friend is a keyword
        // TODO: this might violate the assumption that a keyword can never be a name.
        Some(n) => n,
        None => parse_identifier(context)?,
    };
    let value = if context.tokens.peek() == Tok::Equal {
        context.tokens.advance()?;
        match context.tokens.peek() {
            Tok::AtSign | Tok::True | Tok::False | Tok::NumTypedValue | Tok::ByteStringValue => {
                Some(PragmaValue::Literal(parse_value(context)?))
            }
            Tok::NumValue
                if !context
                    .tokens
                    .lookahead()
                    .map(|tok| tok == Tok::ColonColon)
                    .unwrap_or(false) =>
            {
                Some(PragmaValue::Literal(parse_value(context)?))
            }
            _ => {
                // Parse as a module access for a possibly qualified identifier
                Some(PragmaValue::Ident(parse_name_access_chain(
                    context,
                    || "an identifier as pragma value",
                )?))
            }
        }
    } else {
        None
    };
    let end_loc = context.tokens.tokens_loc();
    Ok(PragmaProperty::new(
        PragmaProperty_ { name, value },
        context.tokens.token_range(start_loc, end_loc),
    ))
}
// If the next token is the specified kind, consume it and return
// its source location.
fn consume_optional_token_with_loc(
    context: &mut Context,
    tok: Tok,
) -> Result<Option<ParsedToken>, Diagnostic> {
    if context.tokens.peek() == tok {
        Ok(Some(context.tokens.advance()?))
    } else {
        Ok(None)
    }
}

// Parse a function parameter:
//      Parameter = <Var> ":" <Type>
pub fn parse_parameter(context: &mut Context) -> Result<(Var, Type), Diagnostic> {
    let v = parse_var(context)?;
    context.tokens.consume_token(Tok::Colon)?;
    let t = parse_type(context)?;
    Ok((v, t))
}

// Parse a function pattern:
//     SpecApplyPattern = <SpecApplyFragment>+ <OptionalTypeArgs>
fn parse_spec_apply_pattern(context: &mut Context) -> Result<SpecApplyPattern, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    // TODO: update the visibility parsing in the spec as well
    let visibility = if context.tokens.peek() == Tok::Public {
        context.tokens.advance()?;
        let vis_end_loc = context.tokens.tokens_loc();
        Some(Visibility::new(
            Visibility_::Public,
            context.tokens.token_range(start_loc, vis_end_loc),
        ))
    } else if context.tokens.peek() == Tok::Identifier && context.tokens.content() == "internal" {
        context.tokens.advance()?;
        let vis_end_loc = context.tokens.tokens_loc();
        Some(Visibility::new(
            Visibility_::Internal,
            context.tokens.token_range(start_loc, vis_end_loc),
        ))
    } else {
        None
    };

    let mut last_end = context.tokens.start_loc() + context.tokens.content().len();
    let name_pattern = parse_list(
        context,
        |context| {
            // We need name fragments followed by each other without space. So we do some
            // magic here similar as with `>>` based on token distance.
            let start_loc = context.tokens.start_loc();
            let adjacent = last_end == start_loc;
            last_end = start_loc + context.tokens.content().len();
            Ok(adjacent && [Tok::Identifier, Tok::Star].contains(&context.tokens.peek()))
        },
        parse_spec_apply_fragment,
    )?;
    let type_parameters = parse_optional_type_parameters(context)?;
    let end_loc = context.tokens.tokens_loc();
    Ok(SpecApplyPattern::new(
        SpecApplyPattern_ {
            visibility,
            name_pattern,
            type_parameters,
        },
        context.tokens.token_range(start_loc, end_loc),
    ))
}

// Parse a name pattern fragment
//     SpecApplyFragment = <Identifier> | "*"
fn parse_spec_apply_fragment(context: &mut Context) -> Result<SpecApplyFragment, Diagnostic> {
    let fragment = match context.tokens.peek() {
        Tok::Identifier => parse_identifier(context)?,
        Tok::Star => context.tokens.advance()?,
        _ => {
            return Err(context
                .tokens
                .unexpected_token_error("a name fragment or `*`"))
        }
    };
    Ok(fragment)
}
