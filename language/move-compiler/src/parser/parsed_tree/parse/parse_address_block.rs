// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

//**************************************************************************************************
// AddressBlock
//**************************************************************************************************

use crate::{
    diagnostics::Diagnostic,
    parser::{
        lexer::Tok,
        parsed_tree::{
            ast::{Address, Address_, Attributes, Definition},
            parse::{parse_identifier::consume_identifier, parse_leading_name_access},
        },
    },
};

use super::{parse_attributes::parse_attributes_vec, parse_module::parse_module_decl, Context};

// Parse an address block:
//      AddressBlock =
//          "address" <LeadingNameAccess> "{" (<Attributes> <Module>)* "}"
//
// Note that "address" is not a token.
fn parse_address_block_decl(
    context: &mut Context,
    attributes: Vec<Attributes>,
) -> Result<Address, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();

    consume_identifier(context, "address")?;

    let address = parse_leading_name_access(context)?;
    context.tokens.previous_end_loc();

    let modules = match context.tokens.peek() {
        Tok::LBrace => {
            context.tokens.advance()?;
            let mut modules = vec![];
            while context.tokens.peek() != Tok::RBrace {
                let attributes = parse_attributes_vec(context)?;
                modules.push(parse_module_decl(context, attributes)?)
            }
            context.tokens.consume_token(Tok::RBrace)?;
            modules
        }
        _ => return Err(context.tokens.unexpected_token_error("'{'")),
    };
    let end_loc = context.tokens.tokens_loc();
    let token_range = context.tokens.token_range(start_loc, end_loc);
    Ok(Address::new(
        Address_ {
            attributes,
            address,
            modules,
        },
        token_range,
    ))
}

pub fn parse_address_block(
    context: &mut Context,
    attributes: Vec<Attributes>,
) -> Result<Definition, Diagnostic> {
    let tree = parse_address_block_decl(context, attributes)?;

    Ok(Definition::Address(tree))
}
