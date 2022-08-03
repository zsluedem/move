// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use move_ir_types::location::Loc;

use crate::{
    diag,
    diagnostics::Diagnostic,
    parser::{
        ast::{BinOp_, QuantKind_},
        lexer::Tok,
        parsed_tree::{
            ast::{
                Attributes, BinOp, Bind, BindList, BindWithRange, BindWithRangeList, Bind_, Block,
                Constant, ConstantDecl, Constant_, Exp, Exp_, Field, LetAssign, LetAssign_,
                LetDeclare, LetDeclare_, ParsedTree, QuantBind, QuantKind, SemicolonEnd,
                SequenceItem, SequenceItem_, SpannedWithComment, Type, UnaryOp, UnaryOp_,
            },
            parse::{parse_comma_list_after_start, parse_spec::parse_spec_block, parse_value},
        },
        syntax::{get_precedence, make_loc},
    },
};

use super::{
    parse_attributes::parse_attributes_vec, parse_comma_list, parse_field,
    parse_friend::parse_friend_decl, parse_identifier, parse_identifier::consume_identifier,
    parse_list, parse_name_access_chain, parse_type::parse_type, parse_use::parse_use_decl,
    parse_var, Context,
};

const MINIMUM_PRECEDENCE: u32 = 1;

// Parse an expression:
//      Exp =
//            <LambdaBindList> <Exp>        spec only
//          | <Quantifier>                  spec only
//          | "if" "(" <Exp> ")" <Exp> ("else" <Exp>)?
//          | "while" "(" <Exp> ")" <Exp> (SpecBlock)?
//          | "loop" <Exp>
//          | "return" <Exp>?
//          | "abort" <Exp>
//          | <BinOpExp>
//          | <UnaryExp> "=" <Exp>
pub fn parse_exp(context: &mut Context) -> Result<Exp, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    let exp_ = match context.tokens.peek() {
        Tok::Pipe => {
            let bindings = parse_lambda_bind_list(context)?;
            let body = Box::new(parse_exp(context)?);
            Exp_::Lambda(bindings, body)
        }
        Tok::Identifier if is_quant(context) => parse_quant(context)?,
        Tok::If => {
            context.tokens.advance()?;
            context.tokens.consume_token(Tok::LParen)?;
            let eb = Box::new(parse_exp(context)?);
            context.tokens.consume_token(Tok::RParen)?;
            let et = Box::new(parse_exp(context)?);
            let ef = if context.tokens.match_token(Tok::Else)? {
                Some(Box::new(parse_exp(context)?))
            } else {
                None
            };
            Exp_::IfElse(eb, et, ef)
        }
        Tok::While => {
            context.tokens.advance()?;
            context.tokens.consume_token(Tok::LParen)?;
            let econd = parse_exp(context)?;
            context.tokens.consume_token(Tok::RParen)?;
            let eloop = Box::new(parse_exp(context)?);
            let espec = if context.tokens.peek() == Tok::Spec {
                Some(parse_spec_block(context, vec![])?)
            } else {
                None
            };
            Exp_::While(Box::new(econd), eloop, espec)
        }
        Tok::Loop => {
            context.tokens.advance()?;
            let eloop = Box::new(parse_exp(context)?);
            Exp_::Loop(eloop)
        }
        Tok::Return => {
            context.tokens.advance()?;
            let e = if at_end_of_exp(context) {
                None
            } else {
                Some(Box::new(parse_exp(context)?))
            };
            Exp_::Return(e)
        }
        Tok::Abort => {
            context.tokens.advance()?;
            let e = Box::new(parse_exp(context)?);
            Exp_::Abort(e)
        }
        _ => {
            // This could be either an assignment or a binary operator
            // expression.
            let lhs = parse_unary_exp(context)?;
            if context.tokens.peek() != Tok::Equal {
                return parse_binop_exp(context, lhs, /* min_prec */ MINIMUM_PRECEDENCE);
            }
            context.tokens.advance()?; // consume the "="
            let rhs = Box::new(parse_exp(context)?);
            Exp_::Assign(Box::new(lhs), rhs)
        }
    };
    let end_loc = context.tokens.tokens_loc();
    let exp = Exp::new(exp_, context.tokens.token_range(start_loc, end_loc));
    Ok(exp)
}

// Parse a list of bindings for lambda.
//      LambdaBindList =
//          "|" Comma<Bind> "|"
fn parse_lambda_bind_list(context: &mut Context) -> Result<BindList, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    let b = parse_comma_list(
        context,
        Tok::Pipe,
        Tok::Pipe,
        parse_bind,
        "a variable or structure binding",
    )?;
    let end_loc = context.tokens.tokens_loc();
    Ok(SpannedWithComment::new(
        b,
        context.tokens.token_range(start_loc, end_loc),
    ))
}

// Parse a binding:
//      Bind =
//          <Var>
//          | <NameAccessChain> <OptionalTypeArgs> "{" Comma<BindField> "}"
fn parse_bind(context: &mut Context) -> Result<Bind, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    if context.tokens.peek() == Tok::Identifier {
        let next_tok = context.tokens.lookahead()?;
        if next_tok != Tok::LBrace && next_tok != Tok::Less && next_tok != Tok::ColonColon {
            let v = Bind_::Var(parse_var(context)?);
            let end_loc = context.tokens.tokens_loc();
            return Ok(Bind::new(v, context.tokens.token_range(start_loc, end_loc)));
        }
    }
    // The item description specified here should include the special case above for
    // variable names, because if the current context cannot be parsed as a struct name
    // it is possible that the user intention was to use a variable name.
    let ty = parse_name_access_chain(context, || "a variable or struct name")?;
    let ty_args = parse_optional_type_args(context)?;
    let args = parse_comma_list(
        context,
        Tok::LBrace,
        Tok::RBrace,
        parse_bind_field,
        "a field binding",
    )?;
    let end_loc = context.tokens.tokens_loc();
    let unpack = Bind_::Unpack(Box::new(ty), ty_args, args);
    Ok(Bind::new(
        unpack,
        context.tokens.token_range(start_loc, end_loc),
    ))
}

// Parse a field name optionally followed by a colon and a binding:
//      BindField = <Field> <":" <Bind>>?
//
// If the binding is not specified, the default is to use a variable
// with the same name as the field.
fn parse_bind_field(context: &mut Context) -> Result<(Field, Option<Bind>), Diagnostic> {
    let f = parse_field(context)?;
    let arg = if context.tokens.match_token(Tok::Colon)? {
        Some(parse_bind(context)?)
    } else {
        None
    };
    Ok((f, arg))
}
// Parse an optional list of type arguments.
//    OptionalTypeArgs = "<" Comma<Type> ">" | <empty>
fn parse_optional_type_args(context: &mut Context) -> Result<Option<Vec<Type>>, Diagnostic> {
    if context.tokens.peek() == Tok::Less {
        Ok(Some(parse_comma_list(
            context,
            Tok::Less,
            Tok::Greater,
            parse_type,
            "a type",
        )?))
    } else {
        Ok(None)
    }
}

// Lookahead to determine whether this is a quantifier. This matches
//
//      ( "exists" | "forall" | "choose" | "min" )
//          <Identifier> ( ":" | <Identifier> ) ...
//
// as a sequence to identify a quantifier. While the <Identifier> after
// the exists/forall would by syntactically sufficient (Move does not
// have affixed identifiers in expressions), we add another token
// of lookahead to keep the result more precise in the presence of
// syntax errors.
fn is_quant(context: &mut Context) -> bool {
    if !matches!(context.tokens.content(), "exists" | "forall" | "choose") {
        return false;
    }
    match context.tokens.lookahead2() {
        Err(_) => false,
        Ok((tok1, tok2)) => tok1 == Tok::Identifier && matches!(tok2, Tok::Colon | Tok::Identifier),
    }
}
// Parses a quantifier expressions, assuming is_quant(context) is true.
//
//   <Quantifier> =
//       ( "forall" | "exists" ) <QuantifierBindings> ({ (<Exp>)* })* ("where" <Exp>)? ":" Exp
//     | ( "choose" [ "min" ] ) <QuantifierBind> "where" <Exp>
//   <QuantifierBindings> = <QuantifierBind> ("," <QuantifierBind>)*
//   <QuantifierBind> = <Identifier> ":" <Type> | <Identifier> "in" <Exp>
//
fn parse_quant(context: &mut Context) -> Result<Exp_, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    let kind = match context.tokens.content() {
        "exists" => {
            context.tokens.advance()?;
            QuantKind_::Exists
        }
        "forall" => {
            context.tokens.advance()?;
            QuantKind_::Forall
        }
        "choose" => {
            context.tokens.advance()?;
            match context.tokens.peek() {
                Tok::Identifier if context.tokens.content() == "min" => {
                    context.tokens.advance()?;
                    QuantKind_::ChooseMin
                }
                _ => QuantKind_::Choose,
            }
        }
        _ => unreachable!(),
    };
    let kind_end_loc = context.tokens.tokens_loc();
    let spanned_kind = QuantKind::new(kind, context.tokens.token_range(start_loc, kind_end_loc));

    if matches!(kind, QuantKind_::Choose | QuantKind_::ChooseMin) {
        let binding_start = context.tokens.tokens_loc();
        let binding = parse_quant_binding(context)?;
        let binding_end = context.tokens.tokens_loc();
        consume_identifier(context, "where")?;
        let body = parse_exp(context)?;
        return Ok(Exp_::Quant(
            spanned_kind,
            BindWithRangeList::new(
                vec![binding],
                context.tokens.token_range(binding_start, binding_end),
            ),
            vec![],
            None,
            Box::new(body),
        ));
    }
    let binds_range_start = context.tokens.tokens_loc();
    let binds_with_range_list = parse_list(
        context,
        |context| {
            if context.tokens.peek() == Tok::Comma {
                context.tokens.advance()?;
                Ok(true)
            } else {
                Ok(false)
            }
        },
        parse_quant_binding,
    )?;
    let binds_range_end = context.tokens.tokens_loc();
    let spanned_binds = BindWithRangeList::new(
        binds_with_range_list,
        context
            .tokens
            .token_range(binds_range_start, binds_range_end),
    );

    let triggers = if context.tokens.peek() == Tok::LBrace {
        parse_list(
            context,
            |context| {
                if context.tokens.peek() == Tok::LBrace {
                    Ok(true)
                } else {
                    Ok(false)
                }
            },
            |context| {
                parse_comma_list(
                    context,
                    Tok::LBrace,
                    Tok::RBrace,
                    parse_exp,
                    "a trigger expresssion",
                )
            },
        )?
    } else {
        Vec::new()
    };

    let condition = match context.tokens.peek() {
        Tok::Identifier if context.tokens.content() == "where" => {
            context.tokens.advance()?;
            Some(Box::new(parse_exp(context)?))
        }
        _ => None,
    };
    context.tokens.consume_token(Tok::Colon)?;
    let body = parse_exp(context)?;

    Ok(Exp_::Quant(
        spanned_kind,
        spanned_binds,
        triggers,
        condition,
        Box::new(body),
    ))
}

// Parses one quantifier binding.
fn parse_quant_binding(context: &mut Context) -> Result<BindWithRange, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    let ident = parse_identifier(context)?;

    if context.tokens.peek() == Tok::Colon {
        // This is a quantifier over the full domain of a type.
        // Built `domain<ty>()` expression.
        context.tokens.advance()?;
        let ty = parse_type(context)?;
        let end_loc = context.tokens.tokens_loc();
        let q = QuantBind::TypeBind(ident, ty);
        Ok(BindWithRange::new(
            q,
            context.tokens.token_range(start_loc, end_loc),
        ))
    } else {
        // This is a quantifier over a value, like a vector or a range.
        consume_identifier(context, "in")?;
        let exp = parse_exp(context)?;
        let end_loc = context.tokens.tokens_loc();
        let q = QuantBind::InBind(ident, exp);
        Ok(BindWithRange::new(
            q,
            context.tokens.token_range(start_loc, end_loc),
        ))
    }
}

// Return true if the current token is one that might occur after an Exp.
// This is needed, for example, to check for the optional Exp argument to
// a return (where "return" is itself an Exp).
fn at_end_of_exp(context: &mut Context) -> bool {
    matches!(
        context.tokens.peek(),
        // These are the tokens that can occur after an Exp. If the grammar
        // changes, we need to make sure that these are kept up to date and that
        // none of these tokens can occur at the beginning of an Exp.
        Tok::Else | Tok::RBrace | Tok::RParen | Tok::Comma | Tok::Colon | Tok::Semicolon
    )
}

// Parse a binary operator expression:
//      BinOpExp =
//          <BinOpExp> <BinOp> <BinOpExp>
//          | <UnaryExp>
//      BinOp = (listed from lowest to highest precedence)
//          "==>"                                       spec only
//          | "||"
//          | "&&"
//          | "==" | "!=" | "<" | ">" | "<=" | ">="
//          | ".."                                      spec only
//          | "|"
//          | "^"
//          | "&"
//          | "<<" | ">>"
//          | "+" | "-"
//          | "*" | "/" | "%"
//
// This function takes the LHS of the expression as an argument, and it
// continues parsing binary expressions as long as they have at least the
// specified "min_prec" minimum precedence.
fn parse_binop_exp(context: &mut Context, lhs: Exp, min_prec: u32) -> Result<Exp, Diagnostic> {
    let mut result = lhs;
    let mut next_tok_prec = get_precedence(context.tokens.peek());

    while next_tok_prec >= min_prec {
        // Parse the operator.
        let op_start_loc = context.tokens.tokens_loc();
        let op_token = context.tokens.peek();
        context.tokens.advance()?;
        let op_end_loc = context.tokens.tokens_loc();

        let mut rhs = parse_unary_exp(context)?;

        // If the next token is another binary operator with a higher
        // precedence, then recursively parse that expression as the RHS.
        let this_prec = next_tok_prec;
        next_tok_prec = get_precedence(context.tokens.peek());
        if this_prec < next_tok_prec {
            rhs = parse_binop_exp(context, rhs, this_prec + 1)?;
            next_tok_prec = get_precedence(context.tokens.peek());
        }

        let op = match op_token {
            Tok::EqualEqual => BinOp_::Eq,
            Tok::ExclaimEqual => BinOp_::Neq,
            Tok::Less => BinOp_::Lt,
            Tok::Greater => BinOp_::Gt,
            Tok::LessEqual => BinOp_::Le,
            Tok::GreaterEqual => BinOp_::Ge,
            Tok::PipePipe => BinOp_::Or,
            Tok::AmpAmp => BinOp_::And,
            Tok::Caret => BinOp_::Xor,
            Tok::Pipe => BinOp_::BitOr,
            Tok::Amp => BinOp_::BitAnd,
            Tok::LessLess => BinOp_::Shl,
            Tok::GreaterGreater => BinOp_::Shr,
            Tok::Plus => BinOp_::Add,
            Tok::Minus => BinOp_::Sub,
            Tok::Star => BinOp_::Mul,
            Tok::Slash => BinOp_::Div,
            Tok::Percent => BinOp_::Mod,
            Tok::PeriodPeriod => BinOp_::Range,
            Tok::EqualEqualGreater => BinOp_::Implies,
            Tok::LessEqualEqualGreater => BinOp_::Iff,
            _ => panic!("Unexpected token that is not a binary operator"),
        };
        let sp_op = BinOp::new(op, context.tokens.token_range(op_start_loc, op_end_loc));

        let start_loc = result.token_range.start;
        let end_loc = context.tokens.tokens_loc();
        let e = Exp_::BinopExp(Box::new(result), sp_op, Box::new(rhs));
        result = Exp::new(e, context.tokens.token_range(start_loc, end_loc));
    }

    Ok(result)
}

// Parse a unary expression:
//      UnaryExp =
//          "!" <UnaryExp>
//          | "&mut" <UnaryExp>
//          | "&" <UnaryExp>
//          | "*" <UnaryExp>
//          | "move" <Var>
//          | "copy" <Var>
//          | <DotOrIndexChain>
pub fn parse_unary_exp(context: &mut Context) -> Result<Exp, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    let unary_op = match context.tokens.peek() {
        Tok::Exclaim => {
            context.tokens.advance()?;
            UnaryOp_::Not
        }
        Tok::AmpMut => {
            context.tokens.advance()?;
            UnaryOp_::BorrowMut
        }
        Tok::Amp => {
            context.tokens.advance()?;
            UnaryOp_::Borrow
        }
        Tok::Star => {
            context.tokens.advance()?;
            UnaryOp_::Dereference
        }
        Tok::Move => {
            context.tokens.advance()?;
            let exp_ = Exp_::Move(parse_var(context)?);
            let end_loc = context.tokens.tokens_loc();
            return Ok(Exp::new(
                exp_,
                context.tokens.token_range(start_loc, end_loc),
            ));
        }
        Tok::Copy => {
            context.tokens.advance()?;
            let exp_ = Exp_::Copy(parse_var(context)?);
            let end_loc = context.tokens.tokens_loc();
            return Ok(Exp::new(
                exp_,
                context.tokens.token_range(start_loc, end_loc),
            ));
        }
        _ => {
            return parse_dot_or_index_chain(context);
        }
    };
    let op_end_loc = context.tokens.tokens_loc();
    let op = UnaryOp::new(unary_op, context.tokens.token_range(start_loc, op_end_loc));
    let e = parse_unary_exp(context)?;
    let exp_ = Exp_::UnaryExp(op, Box::new(e));
    let end_loc = context.tokens.tokens_loc();
    Ok(Exp::new(
        exp_,
        context.tokens.token_range(start_loc, end_loc),
    ))
}

// Parse an expression term optionally followed by a chain of dot or index accesses:
//      DotOrIndexChain =
//          <DotOrIndexChain> "." <Identifier>
//          | <DotOrIndexChain> "[" <Exp> "]"                      spec only
//          | <Term>
fn parse_dot_or_index_chain(context: &mut Context) -> Result<Exp, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    let mut lhs = parse_term(context)?;
    loop {
        let exp = match context.tokens.peek() {
            Tok::Period => {
                context.tokens.advance()?;
                let n = parse_identifier(context)?;
                Exp_::Dot(Box::new(lhs), n)
            }
            Tok::LBracket => {
                context.tokens.advance()?;
                let index = parse_exp(context)?;
                let exp = Exp_::Index(Box::new(lhs), Box::new(index));
                context.tokens.consume_token(Tok::RBracket)?;
                exp
            }
            _ => break,
        };
        let end_loc = context.tokens.tokens_loc();
        lhs = Exp::new(exp, context.tokens.token_range(start_loc, end_loc));
    }
    Ok(lhs)
}

// Parse an expression term:
//      Term =
//          "break"
//          | "continue"
//          | "vector" ("<" Comma<Type> ">")? "[" Comma<Exp> "]"
//          | <Value>
//          | "(" Comma<Exp> ")"
//          | "(" <Exp> ":" <Type> ")"
//          | "(" <Exp> "as" <Type> ")"
//          | "{" <Sequence>
fn parse_term(context: &mut Context) -> Result<Exp, Diagnostic> {
    const VECTOR_IDENT: &str = "vector";

    let start_loc = context.tokens.tokens_loc();
    let term = match context.tokens.peek() {
        Tok::Break => {
            context.tokens.advance()?;
            Exp_::Break
        }

        Tok::Continue => {
            context.tokens.advance()?;
            Exp_::Continue
        }

        Tok::Identifier
            if context.tokens.content() == VECTOR_IDENT
                && matches!(context.tokens.lookahead(), Ok(Tok::Less | Tok::LBracket)) =>
        {
            let name = consume_identifier(context, VECTOR_IDENT)?;
            let targs_start_loc = context.tokens.start_loc();
            let tys_opt = parse_optional_type_args(context).map_err(|diag| {
                let targ_loc =
                    make_loc(context.tokens.file_hash(), targs_start_loc, targs_start_loc);
                add_type_args_ambiguity_label(targ_loc, diag)
            })?;
            let args_start_loc = context.tokens.tokens_loc();
            let args = parse_comma_list(
                context,
                Tok::LBracket,
                Tok::RBracket,
                parse_exp,
                "a vector argument expression",
            )?;
            let args_end_loc = context.tokens.tokens_loc();

            Exp_::Vector(
                name,
                tys_opt,
                SpannedWithComment::new(
                    args,
                    context.tokens.token_range(args_start_loc, args_end_loc),
                ),
            )
        }

        Tok::Identifier => parse_name_exp(context)?,

        Tok::NumValue => {
            // Check if this is a ModuleIdent (in a ModuleAccess).
            if context.tokens.lookahead()? == Tok::ColonColon {
                parse_name_exp(context)?
            } else {
                Exp_::Value(parse_value(context)?)
            }
        }

        Tok::AtSign | Tok::True | Tok::False | Tok::NumTypedValue | Tok::ByteStringValue => {
            Exp_::Value(parse_value(context)?)
        }

        // "(" Comma<Exp> ")"
        // "(" <Exp> ":" <Type> ")"
        // "(" <Exp> "as" <Type> ")"
        Tok::LParen => {
            let list_loc = context.tokens.start_loc();
            context.tokens.advance()?; // consume the LParen
            if context.tokens.match_token(Tok::RParen)? {
                Exp_::Unit
            } else {
                // If there is a single expression inside the parens,
                // then it may be followed by a colon and a type annotation.
                let e = parse_exp(context)?;
                if context.tokens.match_token(Tok::Colon)? {
                    let ty = parse_type(context)?;
                    context.tokens.consume_token(Tok::RParen)?;
                    Exp_::Annotate(Box::new(e), ty)
                } else if context.tokens.match_token(Tok::As)? {
                    let ty = parse_type(context)?;
                    context.tokens.consume_token(Tok::RParen)?;
                    Exp_::Cast(Box::new(e), ty)
                } else {
                    if context.tokens.peek() != Tok::RParen {
                        context.tokens.consume_token(Tok::Comma)?;
                    }
                    let mut es = parse_comma_list_after_start(
                        context,
                        list_loc,
                        Tok::LParen,
                        Tok::RParen,
                        parse_exp,
                        "an expression",
                    )?;
                    if es.is_empty() {
                        e.value
                    } else {
                        es.insert(0, e);
                        Exp_::ExpList(es)
                    }
                }
            }
        }

        // "{" <Sequence>
        Tok::LBrace => Exp_::Block(parse_sequence_block(context)?),

        _ => {
            return Err(context.tokens.unexpected_token_error("an expression term"));
        }
    };
    let end_loc = context.tokens.tokens_loc();

    Ok(Exp::new(
        term,
        context.tokens.token_range(start_loc, end_loc),
    ))
}
fn add_type_args_ambiguity_label(loc: Loc, mut diag: Diagnostic) -> Diagnostic {
    const MSG: &str = "Perhaps you need a blank space before this '<' operator?";
    diag.add_secondary_label((loc, MSG));
    diag
}

// Parse a pack, call, or other reference to a name:
//      NameExp =
//          <NameAccessChain> <OptionalTypeArgs> "{" Comma<ExpField> "}"
//          | <NameAccessChain> <OptionalTypeArgs> "(" Comma<Exp> ")"
//          | <NameAccessChain> "!" "(" Comma<Exp> ")"
//          | <NameAccessChain> <OptionalTypeArgs>
fn parse_name_exp(context: &mut Context) -> Result<Exp_, Diagnostic> {
    let n = parse_name_access_chain(context, || {
        panic!("parse_name_exp with something other than a ModuleAccess")
    })?;

    // There's an ambiguity if the name is followed by a "<". If there is no whitespace
    // after the name, treat it as the start of a list of type arguments. Otherwise
    // assume that the "<" is a boolean operator.
    let mut tys = None;
    let start_loc = context.tokens.start_loc();
    if context.tokens.peek() == Tok::Exclaim {
        context.tokens.advance()?;
        let is_macro = true;
        let start_loc = context.tokens.tokens_loc();
        let rhs = parse_call_args(context)?;
        let end_loc = context.tokens.tokens_loc();
        let token_range = context.tokens.token_range(start_loc, end_loc);
        return Ok(Exp_::Call(
            n,
            is_macro,
            tys,
            SpannedWithComment::new(rhs, token_range),
        ));
    }

    if context.tokens.peek() == Tok::Less
        && context.tokens.previous_end_loc() == context.tokens.start_loc()
    {
        let loc = make_loc(context.tokens.file_hash(), start_loc, start_loc);
        tys = parse_optional_type_args(context)
            .map_err(|diag| add_type_args_ambiguity_label(loc, diag))?;
    }

    match context.tokens.peek() {
        // Pack: "{" Comma<ExpField> "}"
        Tok::LBrace => {
            let fs = parse_comma_list(
                context,
                Tok::LBrace,
                Tok::RBrace,
                parse_exp_field,
                "a field expression",
            )?;
            Ok(Exp_::Pack(n, tys, fs))
        }

        // Call: "(" Comma<Exp> ")"
        Tok::Exclaim | Tok::LParen => {
            let is_macro = false;
            let start_loc = context.tokens.tokens_loc();
            let rhs = parse_call_args(context)?;
            let end_loc = context.tokens.tokens_loc();
            let token_range = context.tokens.token_range(start_loc, end_loc);
            Ok(Exp_::Call(
                n,
                is_macro,
                tys,
                SpannedWithComment::new(rhs, token_range),
            ))
        }

        // Other name reference...
        _ => Ok(Exp_::Name(n, tys)),
    }
}

// Parse the arguments to a call: "(" Comma<Exp> ")"
fn parse_call_args(context: &mut Context) -> Result<Vec<Exp>, Diagnostic> {
    let args = parse_comma_list(
        context,
        Tok::LParen,
        Tok::RParen,
        parse_exp,
        "a call argument expression",
    )?;
    Ok(args)
}

// Parse a field name optionally followed by a colon and an expression argument:
//      ExpField = <Field> <":" <Exp>>?
fn parse_exp_field(context: &mut Context) -> Result<(Field, Option<Exp>), Diagnostic> {
    let f = parse_field(context)?;
    let arg = if context.tokens.match_token(Tok::Colon)? {
        Some(parse_exp(context)?)
    } else {
        None
    };
    Ok((f, arg))
}
// Parse a sequence:
//      Sequence = <UseDecl>* (<SequenceItem> ";")* <Exp>? "}"
//
// Note that this does not include the opening brace of a block but it
// does consume the closing right brace.
pub fn parse_sequence_block(context: &mut Context) -> Result<Block, Diagnostic> {
    let mut seq: Vec<SequenceItem> = vec![];
    context.tokens.consume_token(Tok::LBrace)?;
    while context.tokens.peek() != Tok::RBrace {
        let attributes = parse_attributes_vec(context)?;
        let item_start_loc = context.tokens.tokens_loc();
        let item = parse_sequence_item(context, attributes)?;
        let item_end_loc = context.tokens.tokens_loc();
        let seq_item = SequenceItem::new(
            item,
            context.tokens.token_range(item_start_loc, item_end_loc),
        );
        seq.push(seq_item);
    }
    context.tokens.advance()?; // consume the RBrace
    Ok(seq)
}

fn parse_let(context: &mut Context) -> Result<SequenceItem_, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    context.tokens.consume_token(Tok::Let)?;
    let b = parse_bind_list(context)?;
    let ty_opt = if context.tokens.match_token(Tok::Colon)? {
        Some(parse_type(context)?)
    } else {
        None
    };
    if context.tokens.match_token(Tok::Equal)? {
        let e = parse_exp(context)?;
        context.tokens.consume_token(Tok::Semicolon)?;
        let end_loc = context.tokens.tokens_loc();
        let res = LetAssign_ {
            var: b,
            type_: ty_opt,
            exp: e,
        };
        Ok(SequenceItem_::Bind(LetAssign::new(
            res,
            context.tokens.token_range(start_loc, end_loc),
        )))
    } else {
        context.tokens.consume_token(Tok::Semicolon)?;
        let end_loc = context.tokens.tokens_loc();
        let res = LetDeclare_ {
            var: b,
            type_: ty_opt,
        };
        Ok(SequenceItem_::Declare(LetDeclare::new(
            res,
            context.tokens.token_range(start_loc, end_loc),
        )))
    }
}

// Parse a constant:
//      ConstantDecl = "const" <Identifier> ":" <Type> "=" <Exp> ";"
fn parse_constant_decl(
    context: &mut Context,
    attributes: Vec<Attributes>,
) -> Result<SequenceItem_, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    context.tokens.consume_token(Tok::Const)?;
    let name = parse_identifier(context)?;
    context.tokens.consume_token(Tok::Colon)?;
    let signature = parse_type(context)?;
    context.tokens.consume_token(Tok::Equal)?;
    let exp = parse_exp(context)?;
    context.tokens.consume_token(Tok::Semicolon)?;
    let end_loc = context.tokens.tokens_loc();

    let constant = Constant_ {
        signature,
        name,
        exp,
    };

    Ok(SequenceItem_::Constant(ConstantDecl {
        attributes,
        constant: Constant::new(constant, context.tokens.token_range(start_loc, end_loc)),
    }))
}
// Parse a sequence item:
//      SequenceItem =
//          <Exp>
//          | "let" <BindList> (":" <Type>)? ("=" <Exp>)?
pub fn parse_sequence_item(
    context: &mut Context,
    attributes: Vec<Attributes>,
) -> Result<SequenceItem_, Diagnostic> {
    let token = context.tokens.peek();
    let sequence = match token {
        Tok::Let => {
            if attributes.is_empty() {
                parse_let(context)?
            } else {
                let loc = context.tokens.current_loc();
                return Err(diag!(
                    Declarations::InvalidAttribute,
                    (loc, "attributes before let")
                ));
            }
        }
        Tok::Use => {
            let use_ = parse_use_decl(context, attributes)?;
            SequenceItem_::UseDecl(use_)
        }
        Tok::Const => parse_constant_decl(context, attributes)?,
        Tok::Friend => parse_friend_decl(context, attributes)?,
        Tok::Spec => {
            let spec_block = parse_spec_block(context, attributes)?;
            SequenceItem_::Spec(spec_block)
        }
        _ => {
            if attributes.is_empty() {
                let e = parse_exp(context)?;
                if context.tokens.peek() == Tok::Semicolon {
                    let tok = context.tokens.advance()?;
                    SequenceItem_::Exp(e, SemicolonEnd::IsSemicolonEnd(tok.value))
                } else {
                    SequenceItem_::Exp(e, SemicolonEnd::NotSemicolonEnd)
                }
            } else {
                let loc = context.tokens.current_loc();
                return Err(diag!(
                    Declarations::InvalidAttribute,
                    (loc, "attributes before let")
                ));
            }
        }
    };

    Ok(sequence)
}

pub fn parse_sequence(
    context: &mut Context,
    attributes: Vec<Attributes>,
) -> Result<ParsedTree, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    let tree = parse_sequence_item(context, attributes)?;
    let end_loc = context.tokens.tokens_loc();
    let token_range = context.tokens.token_range(start_loc, end_loc);
    let seq = SequenceItem::new(tree, token_range);
    Ok(ParsedTree::Sequence(seq))
}

// Parse a list of bindings, which can be zero, one, or more bindings:
//      BindList =
//          <Bind>
//          | "(" Comma<Bind> ")"
//
// The list is enclosed in parenthesis, except that the parenthesis are
// optional if there is a single Bind.
fn parse_bind_list(context: &mut Context) -> Result<BindList, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    let b = if context.tokens.peek() != Tok::LParen {
        vec![parse_bind(context)?]
    } else {
        parse_comma_list(
            context,
            Tok::LParen,
            Tok::RParen,
            parse_bind,
            "a variable or structure binding",
        )?
    };
    let end_loc = context.tokens.tokens_loc();

    Ok(SpannedWithComment::new(
        b,
        context.tokens.token_range(start_loc, end_loc),
    ))
}
