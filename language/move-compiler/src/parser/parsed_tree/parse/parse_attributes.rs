// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::{
    diagnostics::Diagnostic,
    parser::{
        lexer::Tok,
        parsed_tree::ast::{Attribute, AttributeValue, Attribute_, Attributes},
    },
};

use super::{
    maybe_parse_value, parse_comma_list, parse_identifier, parse_name_access_chain, Context,
};

pub fn parse_attributes_vec(context: &mut Context) -> Result<Vec<Attributes>, Diagnostic> {
    let mut attrs = vec![];
    while context.tokens.peek() == Tok::NumSign {
        let attr = parse_attributes(context)?;
        attrs.push(attr);
    }
    Ok(attrs)
}

// Parse an attribute value. Either a value literal or a module access
//      AttributeValue =
//          <Value>
//          | <NameAccessChain>
fn parse_attribute_value(context: &mut Context) -> Result<AttributeValue, Diagnostic> {
    if let Some(v) = maybe_parse_value(context)? {
        return Ok(AttributeValue::Value(v));
    }

    let ma = parse_name_access_chain(context, || "attribute name value")?;
    Ok(AttributeValue::ModuleAccess(ma))
}

// Parse a single attribute
//      Attribute =
//          <Identifier>
//          | <Identifier> "=" <AttributeValue>
//          | <Identifier> "(" Comma<Attribute> ")"
fn parse_attribute(context: &mut Context) -> Result<Attribute, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    let n = parse_identifier(context)?;
    let attr_: Attribute_ = match context.tokens.peek() {
        Tok::Equal => {
            context.tokens.advance()?;
            let attr_value = parse_attribute_value(context)?;
            Attribute_::Assigned(n, attr_value)
        }
        Tok::LParen => {
            let start_attr_loc = context.tokens.tokens_loc();
            let args_ = parse_comma_list(
                context,
                Tok::LParen,
                Tok::RParen,
                parse_attribute,
                "attribute",
            )?;
            let end_attr_loc = context.tokens.tokens_loc();
            let attrs = Attributes::new(
                args_,
                context.tokens.token_range(start_attr_loc, end_attr_loc),
            );
            Attribute_::Parameterized(n, attrs)
        }
        _ => Attribute_::Name(n),
    };
    let end_loc = context.tokens.tokens_loc();
    Ok(Attribute::new(
        attr_,
        context.tokens.token_range(start_loc, end_loc),
    ))
}

// Parse attributes. Used to annotate a variety of AST nodes
//      Attributes = ("#" "[" Comma<Attribute> "]")*
pub fn parse_attributes(context: &mut Context) -> Result<Attributes, Diagnostic> {
    let token_start_loc = context.tokens.tokens_loc();
    context.tokens.consume_token(Tok::NumSign)?;
    let attribute = parse_comma_list(
        context,
        Tok::LBracket,
        Tok::RBracket,
        parse_attribute,
        "attribute",
    )?;
    let token_end_loc = context.tokens.tokens_loc();
    let token_range = context.tokens.token_range(token_start_loc, token_end_loc);
    Ok(Attributes::new(attribute, token_range))
}
