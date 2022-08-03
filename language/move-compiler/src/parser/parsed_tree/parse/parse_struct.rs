// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

//**************************************************************************************************
// Structs
//**************************************************************************************************

use crate::{
    diagnostics::Diagnostic,
    parser::{
        lexer::Tok,
        parsed_tree::ast::{
            Attributes, Field, Modifiers, ParsedTree, Struct, StructFields, StructTypeParameter,
            Struct_, Type,
        },
    },
};

use super::{
    parse_comma_list, parse_field,
    parse_identifier::parse_identifier,
    parse_list,
    parse_type::{parse_ability, parse_type, parse_type_parameter},
    Context,
};

// Parse a struct definition:
//      StructDecl =
//          "struct" <StructDefName> ("has" <Ability> (, <Ability>)+)?
//          ("{" Comma<FieldAnnot> "}" | ";")
//      StructDefName =
//          <Identifier> <OptionalTypeParameters>
fn parse_struct_decl(
    modifiers: Modifiers,
    context: &mut Context,
    attributes: Vec<Attributes>,
) -> Result<Struct, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    context.tokens.consume_token(Tok::Struct)?;

    // <StructDefName>
    let name = parse_identifier(context)?;
    let type_parameters = parse_struct_type_parameters(context)?;

    let abilities = if context.tokens.peek() == Tok::Identifier && context.tokens.content() == "has"
    {
        context.tokens.advance()?;
        parse_list(
            context,
            |context| match context.tokens.peek() {
                Tok::Comma => {
                    context.tokens.advance()?;
                    Ok(true)
                }
                Tok::LBrace | Tok::Semicolon => Ok(false),
                _ => Err(context.tokens.unexpected_token_error(&format!(
                    "one of: '{}', '{}', or '{}'",
                    Tok::Comma,
                    Tok::LBrace,
                    Tok::Semicolon
                ))),
            },
            parse_ability,
        )?
    } else {
        vec![]
    };

    let fields: StructFields = if context.tokens.match_token(Tok::Semicolon)? {
        StructFields { members: vec![] }
    } else {
        let list = parse_comma_list(
            context,
            Tok::LBrace,
            Tok::RBrace,
            parse_field_annot,
            "a field",
        )?;
        StructFields { members: list }
    };
    let end_loc = context.tokens.tokens_loc();
    Ok(Struct::new(
        Struct_ {
            attributes,
            modifiers,
            abilities,
            name,
            type_parameters,
            fields,
        },
        context.tokens.token_range(start_loc, end_loc),
    ))
}

// Parse optional struct type parameters:
//    StructTypeParameter = "<" Comma<TypeParameterWithPhantomDecl> ">" | <empty>
fn parse_struct_type_parameters(
    context: &mut Context,
) -> Result<Vec<StructTypeParameter>, Diagnostic> {
    if context.tokens.peek() == Tok::Less {
        parse_comma_list(
            context,
            Tok::Less,
            Tok::Greater,
            parse_type_parameter_with_phantom_decl,
            "a type parameter",
        )
    } else {
        Ok(vec![])
    }
}

// Parse type parameter with optional phantom declaration:
//   TypeParameterWithPhantomDecl = "phantom"? <TypeParameter>
fn parse_type_parameter_with_phantom_decl(
    context: &mut Context,
) -> Result<StructTypeParameter, Diagnostic> {
    let is_phantom =
        if context.tokens.peek() == Tok::Identifier && context.tokens.content() == "phantom" {
            context.tokens.advance()?;
            true
        } else {
            false
        };
    let (name, constraints) = parse_type_parameter(context)?;
    Ok(StructTypeParameter {
        is_phantom,
        name,
        constraints,
    })
}
// Parse a field annotated with a type:
//      FieldAnnot = <DocComments> <Field> ":" <Type>
fn parse_field_annot(context: &mut Context) -> Result<(Field, Type), Diagnostic> {
    let f = parse_field(context)?;
    context.tokens.consume_token(Tok::Colon)?;
    let st = parse_type(context)?;
    Ok((f, st))
}

pub fn parse_struct(
    modifiers: Modifiers,
    context: &mut Context,
    attributes: Vec<Attributes>,
) -> Result<ParsedTree, Diagnostic> {
    let tree = parse_struct_decl(modifiers, context, attributes)?;
    Ok(ParsedTree::Struct(tree))
}
