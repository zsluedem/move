// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::{
    diagnostics::Diagnostic,
    parser::{
        lexer::Tok,
        parsed_tree::ast::{Ability, Name, Type, Type_},
    },
};

use super::{parse_comma_list, parse_identifier, parse_list, parse_name_access_chain, Context};

// Parse optional type parameter list.
//    OptionalTypeParameters = "<" Comma<TypeParameter> ">" | <empty>
pub fn parse_optional_type_parameters(
    context: &mut Context,
) -> Result<Vec<(Name, Vec<Ability>)>, Diagnostic> {
    if context.tokens.peek() == Tok::Less {
        parse_comma_list(
            context,
            Tok::Less,
            Tok::Greater,
            parse_type_parameter,
            "a type parameter",
        )
    } else {
        Ok(vec![])
    }
}

// Parse a type parameter:
//      TypeParameter =
//          <Identifier> <Constraint>?
//      Constraint =
//          ":" <Ability> (+ <Ability>)*
pub fn parse_type_parameter(context: &mut Context) -> Result<(Name, Vec<Ability>), Diagnostic> {
    let n = parse_identifier(context)?;

    let ability_constraints = if context.tokens.match_token(Tok::Colon)? {
        parse_list(
            context,
            |context| match context.tokens.peek() {
                Tok::Plus => {
                    context.tokens.advance()?;
                    Ok(true)
                }
                Tok::Greater | Tok::Comma => Ok(false),
                _ => Err(context.tokens.unexpected_token_error(&format!(
                    "one of: '{}', '{}', or '{}'",
                    Tok::Plus,
                    Tok::Greater,
                    Tok::Comma
                ))),
            },
            parse_ability,
        )?
    } else {
        vec![]
    };
    Ok((n, ability_constraints))
}

// Parse a type ability
//      Ability =
//          <Copy>
//          | "drop"
//          | "store"
//          | "key"
pub fn parse_ability(context: &mut Context) -> Result<Ability, Diagnostic> {
    context.tokens.advance()
}

// Parse a Type:
//      Type =
//          <NameAccessChain> ("<" Comma<Type> ">")?
//          | "&" <Type>
//          | "&mut" <Type>
//          | "|" Comma<Type> "|" Type   (spec only)
//          | "(" Comma<Type> ")"
pub fn parse_type(context: &mut Context) -> Result<Type, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    let t = match context.tokens.peek() {
        Tok::LParen => {
            let ts = parse_comma_list(context, Tok::LParen, Tok::RParen, parse_type, "a type")?;
            Type_::Sequance(ts)
        }
        Tok::Amp => {
            context.tokens.advance()?;
            let t = parse_type(context)?;
            Type_::Ref(false, Box::new(t))
        }
        Tok::AmpMut => {
            context.tokens.advance()?;
            let t = parse_type(context)?;
            Type_::Ref(true, Box::new(t))
        }
        Tok::Pipe => {
            let args = parse_comma_list(context, Tok::Pipe, Tok::Pipe, parse_type, "a type")?;
            let result = parse_type(context)?;
            Type_::Fun(args, Box::new(result))
        }
        _ => {
            let tn = parse_name_access_chain(context, || "a type name")?;
            let tys = if context.tokens.peek() == Tok::Less {
                parse_comma_list(context, Tok::Less, Tok::Greater, parse_type, "a type")?
            } else {
                vec![]
            };
            Type_::Apply(tn, tys)
        }
    };
    let end_loc = context.tokens.tokens_loc();
    Ok(Type::new(t, context.tokens.token_range(start_loc, end_loc)))
}
