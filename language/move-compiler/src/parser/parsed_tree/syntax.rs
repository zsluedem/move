use std::fs::File;
use std::io::Read;

use move_command_line_common::files::FileHash;
use move_ir_types::location::Loc;
use move_symbol_pool::Symbol;

use super::super::cst::*;
use super::lexer::Token;
use crate::diagnostics::{Diagnostics, FilesSourceText};
use crate::parser::ast::{BinOp_, QuantKind_, Visibility as V, ENTRY_MODIFIER};
use crate::parser::comments::verify_string;
use crate::parser::syntax::get_precedence;
use crate::{
    diag,
    diagnostics::Diagnostic,
    parser::{lexer::Tok, parsed_tree::lexer::FidelityLexer, syntax::make_loc},
};

pub struct Context<'input> {
    tokens: &'input mut FidelityLexer<'input>,
}

impl<'input> Context<'input> {
    fn new(tokens: &'input mut FidelityLexer<'input>) -> Self {
        Self { tokens }
    }
}

const MINIMUM_PRECEDENCE: u32 = 1;

fn parse_exp_semicolon(context: &mut Context) -> Result<ParseTree, Diagnostic> {
    let exp = parse_exp(context)?;
    match context.tokens.peek() {
        Tok::Semicolon => {
            let tok = context.tokens.advance()?;
            Ok(ParseTree::Exp(exp, SemicolonEnd::IsSemicolonEnd(tok.value)))
        }
        _ => Ok(ParseTree::Exp(exp, SemicolonEnd::NotSemicolonEnd)),
    }
}

// Parse an expression:
//      Exp =
//            <LambdaBindList> <Exp>        spec only
//          | <Quantifier>                  spec only
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
        _ => {
            // This could be either an assignment or a binary operator
            // expression.
            let lhs = parse_unary_exp(context)?;
            match context.tokens.peek() {
                Tok::Equal => {
                    context.tokens.advance()?; // consume the "="
                    let rhs = Box::new(parse_exp(context)?);
                    Exp_::Assign(Box::new(lhs), rhs)
                }
                Tok::Semicolon => return Ok(lhs),
                _ => return parse_binop_exp(context, lhs, /* min_prec */ MINIMUM_PRECEDENCE),
            }
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
fn parse_optional_type_args(context: &mut Context) -> Result<Vec<Type>, Diagnostic> {
    if context.tokens.peek() == Tok::Less {
        Ok(parse_comma_list(
            context,
            Tok::Less,
            Tok::Greater,
            parse_type,
            "a type",
        )?)
    } else {
        Ok(vec![])
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
//          | "if" "(" <Exp> ")" <Exp> "else" "{" <Exp> "}"
//          | "if" "(" <Exp> ")" "{" <Exp> "}"
//          | "if" "(" <Exp> ")" <Exp> ("else" <Exp>)?
//          | "while" "(" <Exp> ")" "{" <Exp> "}"
//          | "while" "(" <Exp> ")" <Exp> (SpecBlock)?
//          | "loop" <Exp>
//          | "loop" "{" <Exp> "}"
//          | "return" "{" <Exp> "}"
//          | "return" <Exp>?
//          | "abort" "{" <Exp> "}"
//          | "abort" <Exp>
fn parse_term(context: &mut Context) -> Result<Exp, Diagnostic> {
    const VECTOR_IDENT: &str = "vector";

    let start_loc = context.tokens.tokens_loc();
    let term = match context.tokens.peek() {
        tok if is_control_exp(tok) => {
            let (control_exp, ends_in_block) = parse_control_exp(context)?;
            if !ends_in_block || at_end_of_exp(context) {
                return Ok(control_exp);
            }

            return parse_binop_exp(context, control_exp, /* min_prec */ 1);
        }
        Tok::Break => {
            context.tokens.advance()?;
            if at_start_of_exp(context) {
                let mut diag = context
                    .tokens
                    .unexpected_token_error("the end of an expression");
                diag.add_note("'break' with a value is not yet supported");
                return Err(diag);
            }
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
        Tok::LBrace => Exp_::Block(parse_block_trees(context)?),

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

fn is_control_exp(tok: Tok) -> bool {
    matches!(
        tok,
        Tok::If | Tok::While | Tok::Loop | Tok::Return | Tok::Abort
    )
}

// if there is a block, only parse the block, not any subsequent tokens
// e.g.           if (cond) e1 else { e2 } + 1
// should be,    (if (cond) e1 else { e2 }) + 1
// AND NOT,       if (cond) e1 else ({ e2 } + 1)
// But otherwise, if (cond) e1 else e2 + 1
// should be,     if (cond) e1 else (e2 + 1)
fn parse_control_exp(context: &mut Context) -> Result<(Exp, bool), Diagnostic> {
    fn parse_exp_or_sequence(context: &mut Context) -> Result<(Exp, bool), Diagnostic> {
        match context.tokens.peek() {
            Tok::LBrace => {
                let block_start_loc = context.tokens.tokens_loc();
                let block_ = Exp_::Block(parse_block_trees(context)?);
                let block_end_loc = context.tokens.tokens_loc();
                let exp = Exp::new(
                    block_,
                    context.tokens.token_range(block_start_loc, block_end_loc),
                );
                Ok((exp, true))
            }
            _ => Ok((parse_exp(context)?, false)),
        }
    }
    let start_loc = context.tokens.tokens_loc();
    let (exp_, ends_in_block) = match context.tokens.peek() {
        Tok::If => {
            context.tokens.advance()?;
            context.tokens.consume_token(Tok::LParen)?;
            let eb = Box::new(parse_exp(context)?);
            context.tokens.consume_token(Tok::RParen)?;
            let (et, ends_in_block) = parse_exp_or_sequence(context)?;
            let (ef, ends_in_block) = if context.tokens.match_token(Tok::Else)? {
                let (ef, ends_in_block) = parse_exp_or_sequence(context)?;
                (Some(Box::new(ef)), ends_in_block)
            } else {
                (None, ends_in_block)
            };
            (Exp_::IfElse(eb, Box::new(et), ef), ends_in_block)
        }
        Tok::While => {
            context.tokens.advance()?;
            context.tokens.consume_token(Tok::LParen)?;
            let econd = parse_exp(context)?;
            context.tokens.consume_token(Tok::RParen)?;
            let (eloop, ends_in_block) = parse_exp_or_sequence(context)?;
            if context.tokens.peek() == Tok::Spec {
                let espec = Some(parse_spec_block(context)?);
                (Exp_::While(Box::new(econd), Box::new(eloop), espec), false)
            } else {
                (
                    Exp_::While(Box::new(econd), Box::new(eloop), None),
                    ends_in_block,
                )
            }
        }
        Tok::Loop => {
            context.tokens.advance()?;
            let (eloop, ends_in_block) = parse_exp_or_sequence(context)?;
            (Exp_::Loop(Box::new(eloop)), ends_in_block)
        }
        Tok::Return => {
            context.tokens.advance()?;
            let (e, ends_in_block) = if !at_start_of_exp(context) {
                (None, false)
            } else {
                let (e, ends_in_block) = parse_exp_or_sequence(context)?;
                (Some(Box::new(e)), ends_in_block)
            };
            (Exp_::Return(e), ends_in_block)
        }
        Tok::Abort => {
            context.tokens.advance()?;
            let (e, ends_in_block) = parse_exp_or_sequence(context)?;
            (Exp_::Abort(Box::new(e)), ends_in_block)
        }
        _ => unreachable!(),
    };
    let end_loc = context.tokens.tokens_loc();
    let exp = Exp::new(exp_, context.tokens.token_range(start_loc, end_loc));
    Ok((exp, ends_in_block))
}
fn at_start_of_exp(context: &mut Context) -> bool {
    matches!(
        context.tokens.peek(),
        // value
        Tok::NumValue
            | Tok::NumTypedValue
            | Tok::ByteStringValue
            | Tok::Identifier
            | Tok::AtSign
            | Tok::Copy
            | Tok::Move
            | Tok::False
            | Tok::True
            | Tok::Amp
            | Tok::AmpMut
            | Tok::Star
            | Tok::Exclaim
            | Tok::LParen
            | Tok::LBrace
            | Tok::Abort
            | Tok::Break
            | Tok::Continue
            | Tok::If
            | Tok::Loop
            | Tok::Return
            | Tok::While
    )
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
//          | <NameAccessChain> <OptionalTypeArgs> (: <Type>)?
fn parse_name_exp(context: &mut Context) -> Result<Exp_, Diagnostic> {
    let n = parse_name_access_chain(context, || {
        panic!("parse_name_exp with something other than a ModuleAccess")
    })?;

    // There's an ambiguity if the name is followed by a "<". If there is no whitespace
    // after the name, treat it as the start of a list of type arguments. Otherwise
    // assume that the "<" is a boolean operator.
    let mut tys = vec![];
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

        // : <Type>
        Tok::Colon => {
            context.tokens.consume_token(Tok::Colon)?;
            let type_ = parse_type(context)?;
            Ok(Exp_::Announce(n, tys, type_))
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

fn parse_let(context: &mut Context) -> Result<ParseTree, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    context.tokens.consume_token(Tok::Let)?;
    let is_post = if context.tokens.peek() == Tok::Identifier && context.tokens.content() == "post"
    {
        context.tokens.advance()?;
        true
    } else {
        false
    };
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
            is_post,
            type_: ty_opt,
            exp: e,
        };
        Ok(ParseTree::LetAssign(LetAssign::new(
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
        Ok(ParseTree::Declare(LetDeclare::new(
            res,
            context.tokens.token_range(start_loc, end_loc),
        )))
    }
}

// Parse a constant:
//      ConstantDecl = "const" <Identifier> ":" <Type> "=" <Exp> ";"
fn parse_constant(context: &mut Context) -> Result<ParseTree, Diagnostic> {
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

    Ok(ParseTree::Constant(Constant::new(
        constant,
        context.tokens.token_range(start_loc, end_loc),
    )))
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

// Parse an optional specification block:
//     SpecBlockTarget =
//          <Identifier>
//        |  "fun" <Identifier>  # deprecated
//        | "struct <Identifier> # deprecated
//        | "module"
//        | "schema" <Identifier> <OptionalTypeParameters>
//        | <empty>
//     SpecBlock =
//        <DocComments> "spec" ( <SpecFunction> | <SpecBlockTarget> "{" SpecMember* "}" )
pub fn parse_spec_block(context: &mut Context) -> Result<SpecBlock, Diagnostic> {
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
            let type_parameters = parse_optional_type_args(context)?;
            SpecBlockTarget_::Schema(name, type_parameters)
        }
        Tok::Identifier => {
            let name = parse_identifier(context)?;
            match context.tokens.peek() {
                Tok::ColonColon => {
                    context.tokens.consume_token(Tok::ColonColon)?;
                    let module_name = parse_module_name(context)?;
                    SpecBlockTarget_::IdentModule(name, module_name)
                }
                _ => {
                    let signature = parse_spec_target_signature_opt(context)?;
                    SpecBlockTarget_::Member(name, signature)
                }
            }
        }
        Tok::NumValue => {
            let addr = context.tokens.advance()?;
            context.tokens.consume_token(Tok::ColonColon)?;
            let module_name = parse_module_name(context)?;
            SpecBlockTarget_::IdentModule(addr, module_name)
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

    let members = parse_block_trees(context)?;
    let end_loc = context.tokens.tokens_loc();
    let spec = SpecBlock_ { target, members };
    Ok(SpecBlock::new(
        spec,
        context.tokens.token_range(start_loc, end_loc),
    ))
}

fn parse_spec(context: &mut Context) -> Result<ParseTree, Diagnostic> {
    let spec = parse_spec_block(context)?;
    Ok(ParseTree::Spec(spec))
}

// Parse an invariant:
//     Invariant = "invariant" <OptionalTypeParameters> [ "update" ] <ConditionProperties> <Exp> ";"
fn parse_invariant(context: &mut Context) -> Result<ParseTree, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    context.tokens.consume_token(Tok::Invariant)?;
    let types = parse_optional_type_args(context)?;
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
    Ok(ParseTree::SpecMember(SpecMember::new(
        SpecMember_::Condition(Box::new(kind)),
        token_range,
    )))
}

// Parse a specification condition:
//    SpecCondition =
//        ("assert" | "assume" | "ensures" | "requires" | "decreases"| "succeeds_if" ) <ConditionProperties> <Exp> ";"

fn parse_single_condition(
    context: &mut Context,
    kind: SingleSpecCondition,
) -> Result<ParseTree, Diagnostic> {
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
    Ok(ParseTree::SpecMember(SpecMember::new(
        SpecMember_::Condition(Box::new(con)),
        token_range,
    )))
}
// Parse a specification condition:
//    SpecCondition =
//      "aborts_with" | "modifies" <ConditionProperties> <Exp> [Comma <Exp>]* ";"
fn parse_comma_spec_condition(
    context: &mut Context,
    kind: CommaSpecCondition,
) -> Result<ParseTree, Diagnostic> {
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

    Ok(ParseTree::SpecMember(SpecMember::new(
        SpecMember_::Condition(Box::new(con)),
        token_range,
    )))
}

// Parse an aborts_if specification condition:
//      "aborts_if" <ConditionProperties> <Exp> ["with" <Exp>] ";"
fn parse_abort_if(context: &mut Context) -> Result<ParseTree, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
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
    Ok(ParseTree::SpecMember(SpecMember::new(
        SpecMember_::Condition(Box::new(con)),
        token_range,
    )))
}

// Parse an emits specification condition:
//      "emits" <ConditionProperties> <Exp> ["with" <Exp>] ";"
fn parse_emits(context: &mut Context) -> Result<ParseTree, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
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

    Ok(ParseTree::SpecMember(SpecMember::new(
        SpecMember_::Condition(Box::new(con)),
        token_range,
    )))
}

// Parse an axiom:
//     a = "axiom" <OptionalTypeParameters> <ConditionProperties> <Exp> ";"
fn parse_axiom(context: &mut Context) -> Result<ParseTree, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    consume_identifier(context, "axiom")?;
    let types = parse_optional_type_args(context)?;
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

    Ok(ParseTree::SpecMember(SpecMember::new(
        SpecMember_::Condition(Box::new(con)),
        token_range,
    )))
}
// Parse a specification schema include.
//    SpecInclude = "include" <Exp>
fn parse_spec_include(context: &mut Context) -> Result<ParseTree, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    consume_identifier(context, "include")?;
    let properties = parse_condition_properties(context)?;
    let exp = parse_exp(context)?;
    context.tokens.consume_token(Tok::Semicolon)?;
    let end_loc = context.tokens.tokens_loc();
    let token_range = context.tokens.token_range(start_loc, end_loc);
    Ok(ParseTree::SpecMember(SpecMember::new(
        SpecMember_::Include { properties, exp },
        token_range,
    )))
}

// Parse a specification schema apply.
//    SpecApply = "apply" <Exp> "to" Comma<SpecApplyPattern>
//                                   ( "except" Comma<SpecApplyPattern> )? ";"
fn parse_spec_apply(context: &mut Context) -> Result<ParseTree, Diagnostic> {
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
    let value = SpecMember_::Apply {
        exp,
        patterns,
        exclusion_patterns,
    };
    Ok(ParseTree::SpecMember(SpecMember::new(
        value,
        context.tokens.token_range(start_loc, end_loc),
    )))
}

// Parse a specification pragma:
//    SpecPragma = "pragma" Comma<SpecPragmaProperty> ";"
fn parse_spec_pragma(context: &mut Context) -> Result<ParseTree, Diagnostic> {
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
    let spec = SpecMember_::Pragma { properties };
    Ok(ParseTree::SpecMember(SpecMember::new(
        spec,
        context.tokens.token_range(start_loc, end_loc),
    )))
}

// Parse a specification variable.
//     SpecVariable = ( "global" | "local" )?
//                    <Identifier> <OptionalTypeParameters>
//                    ":" <Type>
//                    [ "=" Exp ]  // global only
//                    ";"
fn parse_spec_variable(context: &mut Context) -> Result<ParseTree, Diagnostic> {
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
    let type_parameters = parse_optional_type_args(context)?;
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
    let spec = SpecMember_::Variable {
        is_global,
        name,
        type_parameters,
        type_,
        init,
    };
    Ok(ParseTree::SpecMember(SpecMember::new(
        spec,
        context.tokens.token_range(start_loc, end_loc),
    )))
}
// Parse a specification update.
//     SpecUpdate = "update" <Exp> = <Exp> ";"
fn parse_spec_update(context: &mut Context) -> Result<ParseTree, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    context.tokens.consume_token(Tok::Identifier)?;
    let lhs = parse_unary_exp(context)?;
    context.tokens.consume_token(Tok::Equal)?;
    let rhs = parse_exp(context)?;
    context.tokens.consume_token(Tok::Semicolon)?;
    let end_loc = context.tokens.tokens_loc();
    let spec = SpecMember_::Update { lhs, rhs };
    Ok(ParseTree::SpecMember(SpecMember::new(
        spec,
        context.tokens.token_range(start_loc, end_loc),
    )))
}

fn parse_spec_target_signature_opt(
    context: &mut Context,
) -> Result<Option<Box<FunctionSignature>>, Diagnostic> {
    match context.tokens.peek() {
        Tok::Less | Tok::LParen => {
            let type_parameters = parse_optional_type_args(context)?;
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
    let type_parameters = parse_optional_type_args(context)?;
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

// Parse a function parameter:
//      Parameter = <Var> ":" <Type>
pub fn parse_parameter(context: &mut Context) -> Result<(Var, Type), Diagnostic> {
    let v = parse_var(context)?;
    context.tokens.consume_token(Tok::Colon)?;
    let t = parse_type(context)?;
    Ok((v, t))
}
// Parse an address block:
//      AddressBlock =
//          "address" <LeadingNameAccess> "{" (<ParseTree>)* "}"
//
// Note that "address" is not a token.
fn parse_address_block_decl(context: &mut Context) -> Result<Address, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();

    consume_identifier(context, "address")?;

    let address = parse_leading_name_access(context)?;
    context.tokens.previous_end_loc();

    let modules = parse_block_trees(context)?;
    let end_loc = context.tokens.tokens_loc();
    let token_range = context.tokens.token_range(start_loc, end_loc);
    Ok(Address::new(Address_ { address, modules }, token_range))
}

pub fn parse_address_block(context: &mut Context) -> Result<ParseTree, Diagnostic> {
    let tree = parse_address_block_decl(context)?;

    Ok(ParseTree::Address(tree))
}

// Parse a function declaration:
//      FunctionDecl =
//          "fun"
//          <FunctionDefName> "(" Comma<Parameter> ")"
//          (":" <Type>)?
//          ("acquires" <NameAccessChain> ("," <NameAccessChain>)*)?
//          ("{" <ParseTree> "}" | ";")
//
fn parse_function_decl(
    modifiers: Modifiers,
    context: &mut Context,
) -> Result<Function, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();

    // "fun" <FunctionDefName>
    context.tokens.consume_token(Tok::Fun)?;
    let name = parse_identifier(context)?;
    let type_parameters = parse_optional_type_args(context)?;

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

    // ("acquires" (<NameAccessChain> ",")* <NameAccessChain> ","?
    let mut acquires = vec![];
    if context.tokens.match_token(Tok::Acquires)? {
        let follows_acquire = |tok| matches!(tok, Tok::Semicolon | Tok::LBrace);
        loop {
            acquires.push(parse_name_access_chain(context, || {
                "a resource struct name"
            })?);
            if follows_acquire(context.tokens.peek()) {
                break;
            }
            context.tokens.consume_token(Tok::Comma)?;
            if follows_acquire(context.tokens.peek()) {
                break;
            }
        }
    }

    let body_start_loc = context.tokens.tokens_loc();
    let body = if context.tokens.match_token(Tok::Semicolon)? {
        let body_end_loc = context.tokens.tokens_loc();

        FunctionBody::new(
            FunctionBody_ {
                body: SpannedWithComment::new(
                    vec![],
                    context.tokens.token_range(body_start_loc, body_end_loc),
                ),
                is_native: true,
            },
            context.tokens.token_range(body_start_loc, body_end_loc),
        )
    } else {
        let seq = parse_block_trees(context)?;
        let body_end_loc = context.tokens.tokens_loc();
        FunctionBody::new(
            FunctionBody_ {
                body: seq,
                is_native: false,
            },
            context.tokens.token_range(body_start_loc, body_end_loc),
        )
    };

    let signatures = FunctionSignature {
        type_parameters,
        parameters,
        return_type,
    };
    let end_loc = context.tokens.tokens_loc();
    let token_range = context.tokens.token_range(start_loc, end_loc);
    Ok(Function::new(
        Function_ {
            modifiers,
            signatures,
            acquires,
            name,
            body,
        },
        token_range,
    ))
}
pub fn parse_function(
    modifiers: Modifiers,
    context: &mut Context,
) -> Result<ParseTree, Diagnostic> {
    let tree = parse_function_decl(modifiers, context)?;

    Ok(ParseTree::Function(tree))
}

// Parse a script:
//      Script =
//          "script" "{"
//              (<ParseTree>)*
//          "}"
pub fn parse_script(context: &mut Context) -> Result<ParseTree, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    context.tokens.consume_token(Tok::Script)?;

    let body = parse_block_trees(context)?;
    let end_loc = context.tokens.tokens_loc();
    let token_range = context.tokens.token_range(start_loc, end_loc);
    let tree = Script::new(Script_ { members: body }, token_range);

    Ok(ParseTree::Script(tree))
}

// Parse a struct definition:
//      StructDecl =
//          "struct" <StructDefName> ("has" <Ability> (, <Ability>)+)?
//          ("{" Comma<FieldAnnot> "}" | ";")
//      StructDefName =
//          <Identifier> <OptionalTypeParameters>
fn parse_struct_decl(modifiers: Modifiers, context: &mut Context) -> Result<Struct, Diagnostic> {
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

pub fn parse_struct(modifiers: Modifiers, context: &mut Context) -> Result<ParseTree, Diagnostic> {
    let tree = parse_struct_decl(modifiers, context)?;
    Ok(ParseTree::Struct(tree))
}

// Parse a use declaration:
//      UseDecl =
//          "use" <ModuleIdent> <UseAlias> ";" |
//          "use" <ModuleIdent> :: <UseMember> ";" |
//          "use" <ModuleIdent> :: "{" Comma<UseMember> "}" ";"
pub fn parse_use(context: &mut Context) -> Result<ParseTree, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    context.tokens.consume_token(Tok::Use)?;
    let ident = parse_module_ident(context)?;
    let alias_opt = parse_use_alias(context)?;
    let use_ = match (&alias_opt, context.tokens.peek()) {
        (None, Tok::ColonColon) => {
            context.tokens.consume_token(Tok::ColonColon)?;
            let sub_uses = match context.tokens.peek() {
                Tok::LBrace => parse_comma_list(
                    context,
                    Tok::LBrace,
                    Tok::RBrace,
                    parse_use_member,
                    "a module member alias",
                )?,
                _ => vec![parse_use_member(context)?],
            };
            Use::Members(ident, sub_uses)
        }
        _ => Use::Module(ident, alias_opt),
    };
    context.tokens.consume_token(Tok::Semicolon)?;
    let end_loc = context.tokens.tokens_loc();
    Ok(ParseTree::UseDecl(UseDecl::new(
        use_,
        context.tokens.token_range(start_loc, end_loc),
    )))
}

// Parse an 'as' use alias:
//      UseAlias = ("as" <Identifier>)?
fn parse_use_alias(context: &mut Context) -> Result<Option<Name>, Diagnostic> {
    Ok(if context.tokens.peek() == Tok::As {
        context.tokens.advance()?;
        Some(parse_identifier(context)?)
    } else {
        None
    })
}

// Parse a module identifier:
//      ModuleIdent = <LeadingNameAccess> "::" <ModuleName>
fn parse_module_ident(context: &mut Context) -> Result<ModuleIdent, Diagnostic> {
    let start_loc = context.tokens.start_loc();
    let address = parse_leading_name_access(context)?;

    context.tokens.consume_token_(
        Tok::ColonColon,
        start_loc,
        " after an address in a module identifier",
    )?;
    let module = parse_module_name(context)?;
    Ok(ModuleIdent { address, module })
}
// Parse an alias for a module member:
//      UseMember = <Identifier> <UseAlias>
fn parse_use_member(context: &mut Context) -> Result<(Name, Option<Name>), Diagnostic> {
    let member = parse_identifier(context)?;
    let alias_opt = parse_use_alias(context)?;
    Ok((member, alias_opt))
}

// Parse a friend declaration:
//      FriendDecl =
//          "friend" <NameAccessChain> ";"
fn parse_friend(context: &mut Context) -> Result<ParseTree, Diagnostic> {
    let token_start_loc = context.tokens.tokens_loc();

    context.tokens.consume_token(Tok::Friend)?;
    let friend = parse_name_access_chain(context, || "a friend declaration")?;
    context.tokens.consume_token(Tok::Semicolon)?;
    let token_end_loc = context.tokens.tokens_loc();
    let token_range = context.tokens.token_range(token_start_loc, token_end_loc);

    Ok(ParseTree::FriendDecl(FriendDecl::new(friend, token_range)))
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
fn parse_attributes(context: &mut Context) -> Result<ParseTree, Diagnostic> {
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
    Ok(ParseTree::Attribute(Attributes::new(
        attribute,
        token_range,
    )))
}

// Parse abilities
//      Abilites =
//          ":" <Ability> (+ <Ability>)*
fn parse_abilities(context: &mut Context) -> Result<Vec<Ability>, Diagnostic> {
    if context.tokens.match_token(Tok::Colon)? {
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
fn parse_type_parameter(context: &mut Context) -> Result<(Name, Vec<Ability>), Diagnostic> {
    let n = parse_identifier(context)?;

    let ability_constraints = parse_abilities(context)?;
    Ok((n, ability_constraints))
}

// Parse a type ability
//      Ability =
//          <Copy>
//          | "drop"
//          | "store"
//          | "key"
fn parse_ability(context: &mut Context) -> Result<Ability, Diagnostic> {
    context.tokens.advance()
}

// Parse a Type:
//      Type =
//          <NameAccessChain> ("<" Comma<Type> ">")?
//          | <NameAccessChain> : <Ability>*?
//          | "&" <Type>
//          | "&mut" <Type>
//          | "|" Comma<Type> "|" Type   (spec only)
//          | "(" Comma<Type> ")"
fn parse_type(context: &mut Context) -> Result<Type, Diagnostic> {
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
            match context.tokens.peek() {
                Tok::Less => {
                    let tys =
                        parse_comma_list(context, Tok::Less, Tok::Greater, parse_type, "a type")?;
                    Type_::Apply(tn, tys)
                }
                Tok::Colon => {
                    let abilities = parse_abilities(context)?;
                    Type_::Ability(tn, abilities)
                }
                _ => Type_::Apply(tn, vec![]),
            }
        }
    };
    let end_loc = context.tokens.tokens_loc();
    Ok(Type::new(t, context.tokens.token_range(start_loc, end_loc)))
}

// Parse an identifier:
//      Identifier = <IdentifierValue>
fn parse_identifier(context: &mut Context) -> Result<ParsedToken, Diagnostic> {
    if context.tokens.peek() != Tok::Identifier {
        return Err(context.tokens.unexpected_token_error("an identifier"));
    }
    let token = context.tokens.advance()?;
    Ok(token)
}
// Check for the identifier token with specified value and return an error if it does not match.
fn consume_identifier(context: &mut Context, value: &str) -> Result<ParsedToken, Diagnostic> {
    if context.tokens.peek() == Tok::Identifier && context.tokens.content() == value {
        context.tokens.advance()
    } else {
        let expected = format!("'{}'", value);
        Err(context.tokens.unexpected_token_error(&expected))
    }
}

fn match_identifier(context: &mut Context, value: &str) -> Result<bool, Diagnostic> {
    if context.tokens.peek() == Tok::Identifier && context.tokens.content() == value {
        context.tokens.advance()?;
        Ok(true)
    } else {
        Ok(false)
    }
}

// Parse module member modifiers: visiblility and native.
// The modifiers are also used for script-functions
//      ModuleMemberModifiers = <ModuleMemberModifier>*
//      ModuleMemberModifier = <Visibility> | "native"
// ModuleMemberModifiers checks for uniqueness, meaning each individual ModuleMemberModifier can
// appear only once
fn parse_module_member_modifiers(context: &mut Context) -> Result<Modifiers, Diagnostic> {
    let mut mods = vec![];
    loop {
        match context.tokens.peek() {
            Tok::Public => {
                let start_loc = context.tokens.tokens_loc();
                let visibility = parse_visibility(context)?;
                let end_loc = context.tokens.tokens_loc();
                mods.push(Modifier::new(
                    Modifier_::Visibility(visibility),
                    context.tokens.token_range(start_loc, end_loc),
                ))
            }
            Tok::Native => {
                let modifier = context.tokens.advance()?;
                mods.push(Modifier::new(Modifier_::Native, modifier.token_range))
            }
            Tok::Identifier if context.tokens.content() == ENTRY_MODIFIER => {
                let modifier = context.tokens.advance()?;
                mods.push(Modifier::new(Modifier_::Entry, modifier.token_range))
            }
            _ => break,
        }
    }
    Ok(mods)
}

// Parse a function visibility modifier:
//      Visibility = "public" ( "(" "script" | "friend" ")" )?
fn parse_visibility(context: &mut Context) -> Result<Visibility, Diagnostic> {
    let start_loc = context.tokens.start_loc();
    let start_tokens_loc = context.tokens.tokens_loc();
    context.tokens.consume_token(Tok::Public)?;
    let sub_public_vis = if context.tokens.match_token(Tok::LParen)? {
        let sub_token = context.tokens.peek();
        context.tokens.advance()?;
        if sub_token != Tok::RParen {
            context.tokens.consume_token(Tok::RParen)?;
        }
        Some(sub_token)
    } else {
        None
    };
    let end_tokens_loc = context.tokens.tokens_loc();
    // this loc will cover the span of 'public' or 'public(...)' in entirety
    let end_loc = context.tokens.previous_end_loc();
    // this loc will cover the span of 'public' or 'public(...)' in entirety
    let loc = make_loc(context.tokens.file_hash(), start_loc, end_loc);
    let vis = match sub_public_vis {
        None => Visibility_::Public,
        Some(Tok::Script) => Visibility_::Script,
        Some(Tok::Friend) => Visibility_::Friend,
        _ => {
            let msg = format!(
                "Invalid visibility modifier. Consider removing it or using '{}' or '{}'",
                V::PUBLIC,
                V::FRIEND
            );
            return Err(diag!(Syntax::UnexpectedToken, (loc, msg)));
        }
    };
    Ok(Visibility::new(
        vis,
        context.tokens.token_range(start_tokens_loc, end_tokens_loc),
    ))
}

// Parse a module name:
//      ModuleName = <Identifier>
fn parse_module_name(context: &mut Context) -> Result<ParsedToken, Diagnostic> {
    parse_identifier(context)
}

// Parse a module:
//      Module =
//          <DocComments>  "module" (<LeadingNameAccess>::)?<ModuleName> "{"
//              <ParseTree>*
//          "}"
fn parse_module(context: &mut Context) -> Result<ParseTree, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    context.tokens.consume_token(Tok::Module)?;
    let leading = parse_leading_name_access(context)?;
    let (name, address) = if context.tokens.match_token(Tok::ColonColon)? {
        (parse_module_name(context)?, Some(leading))
    } else {
        (leading, None)
    };

    let body = parse_block_trees(context)?;
    let end_loc = context.tokens.tokens_loc();
    let token_range = context.tokens.token_range(start_loc, end_loc);
    let tree = Module::new(
        Module_ {
            address,
            name,
            body,
        },
        token_range,
    );

    Ok(ParseTree::Module(tree))
}

fn parse_block_trees(context: &mut Context) -> Result<BlockSequence, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    context.tokens.consume_token(Tok::LBrace)?;

    let mut members = vec![];
    while context.tokens.peek() != Tok::RBrace {
        members.push(parse_tree(context)?);
    }
    context.tokens.consume_token(Tok::RBrace)?;
    let end_loc = context.tokens.tokens_loc();
    Ok(SpannedWithComment::new(
        members,
        context.tokens.token_range(start_loc, end_loc),
    ))
}

fn parse_modifier_follow(context: &mut Context) -> Result<ParseTree, Diagnostic> {
    let modifiers = parse_module_member_modifiers(context)?;
    match context.tokens.peek() {
        Tok::Fun => parse_function(modifiers, context),
        Tok::Struct => parse_struct(modifiers, context),
        _ => Err(context.tokens.unexpected_token_error("a fun or a struct")),
    }
}

// Parse the beginning of an access, either an address or an identifier:
//      LeadingNameAccess = <NumericalAddress> | <Identifier>
fn parse_leading_name_access(context: &mut Context) -> Result<LeadingNameAccess, Diagnostic> {
    parse_leading_name_access_(context, || "an address or an identifier")
}

// Parse the beginning of an access, either an address or an identifier with a specific description
fn parse_leading_name_access_<'a, F: FnOnce() -> &'a str>(
    context: &mut Context,
    item_description: F,
) -> Result<LeadingNameAccess, Diagnostic> {
    match context.tokens.peek() {
        Tok::Identifier | Tok::NumValue => {
            let addr = context.tokens.advance()?;
            Ok(addr)
        }
        _ => Err(context.tokens.unexpected_token_error(item_description())),
    }
}

// Parse a value:
//      Value =
//          "@" <LeadingAccessName>
//          | "true"
//          | "false"
//          | <Number>
//          | <NumberTyped>
//          | <ByteString>
fn maybe_parse_value(context: &mut Context) -> Result<Option<Value>, Diagnostic> {
    match context.tokens.peek() {
        Tok::AtSign => {
            let start_token_index = context.tokens.tokens_loc();
            context.tokens.advance()?;
            let addr = parse_leading_name_access(context)?;
            let end_token_index = context.tokens.tokens_loc();
            Ok(Some(Value::new(
                Value_::Address(addr),
                context
                    .tokens
                    .token_range(start_token_index, end_token_index),
            )))
        }
        Tok::True | Tok::False | Tok::NumTypedValue | Tok::ByteStringValue => {
            let lit = context.tokens.advance()?;
            Ok(Some(Value::new(
                Value_::Literal(lit.value),
                lit.token_range,
            )))
        }
        Tok::NumValue => {
            //  If the number is followed by "::", parse it as the beginning of an address access
            if let Ok(Tok::ColonColon) = context.tokens.lookahead() {
                return Ok(None);
            }
            let lit = context.tokens.advance()?;
            Ok(Some(Value::new(
                Value_::Literal(lit.value),
                lit.token_range,
            )))
        }
        _ => Ok(None),
    }
}
fn parse_value(context: &mut Context) -> Result<Value, Diagnostic> {
    Ok(maybe_parse_value(context)?.expect("parse_value called with invalid token"))
}

// Parse a module access (a variable, struct type, or function):
//      NameAccessChain = <LeadingNameAccess> ( "::" <Identifier> ( "::" <Identifier> )? )?
fn parse_name_access_chain<'a, F: FnOnce() -> &'a str>(
    context: &mut Context,
    item_description: F,
) -> Result<NameAccessChain, Diagnostic> {
    let start_loc = context.tokens.tokens_loc();
    let ln = parse_leading_name_access_(context, item_description)?;
    let mut names = vec![ln];
    while context.tokens.peek() == Tok::ColonColon {
        context.tokens.consume_token(Tok::ColonColon)?;
        let name = parse_identifier(context)?;
        names.push(name)
    }
    let end_loc = context.tokens.tokens_loc();
    Ok(NameAccessChain::new(
        names,
        context.tokens.token_range(start_loc, end_loc),
    ))
}
fn parse_comma_list<F, R>(
    context: &mut Context,
    start_token: Tok,
    end_token: Tok,
    parse_list_item: F,
    item_description: &str,
) -> Result<Vec<R>, Diagnostic>
where
    F: Fn(&mut Context) -> Result<R, Diagnostic>,
{
    let start_loc = context.tokens.start_loc();
    context.tokens.consume_token(start_token)?;
    parse_comma_list_after_start(
        context,
        start_loc,
        start_token,
        end_token,
        parse_list_item,
        item_description,
    )
}

// Parse a comma-separated list of items, including the specified ending token, but
// assuming that the starting token has already been consumed.
fn parse_comma_list_after_start<F, R>(
    context: &mut Context,
    start_loc: usize,
    start_token: Tok,
    end_token: Tok,
    parse_list_item: F,
    item_description: &str,
) -> Result<Vec<R>, Diagnostic>
where
    F: Fn(&mut Context) -> Result<R, Diagnostic>,
{
    context.tokens.adjust_token(end_token);
    if context.tokens.match_token(end_token)? {
        return Ok(vec![]);
    }
    let mut v = vec![];
    loop {
        if context.tokens.peek() == Tok::Comma {
            let loc = context.tokens.current_loc();
            return Err(diag!(
                Syntax::UnexpectedToken,
                (loc, format!("Expected {}", item_description))
            ));
        }
        v.push(parse_list_item(context)?);
        context.tokens.adjust_token(end_token);
        if context.tokens.match_token(end_token)? {
            break Ok(v);
        }
        if !context.tokens.match_token(Tok::Comma)? {
            let loc = context.tokens.current_loc();
            let loc2 = make_loc(context.tokens.file_hash(), start_loc, start_loc);
            return Err(diag!(
                Syntax::UnexpectedToken,
                (loc, format!("Expected '{}'", end_token)),
                (loc2, format!("To match this '{}'", start_token)),
            ));
        }
        context.tokens.adjust_token(end_token);
        if context.tokens.match_token(end_token)? {
            break Ok(v);
        }
    }
}

// Parse a list of items, without specified start and end tokens, and the separator determined by
// the passed function `parse_list_continue`.
fn parse_list<C, F, R>(
    context: &mut Context,
    mut parse_list_continue: C,
    parse_list_item: F,
) -> Result<Vec<R>, Diagnostic>
where
    C: FnMut(&mut Context) -> Result<bool, Diagnostic>,
    F: Fn(&mut Context) -> Result<R, Diagnostic>,
{
    let mut v = vec![];
    loop {
        v.push(parse_list_item(context)?);
        if !parse_list_continue(context)? {
            break Ok(v);
        }
    }
}

// Parse a field name:
//      Field = <Identifier>
fn parse_field(context: &mut Context) -> Result<Field, Diagnostic> {
    parse_identifier(context)
}

// Parse a variable name:
//      Var = <Identifier>
fn parse_var(context: &mut Context) -> Result<Var, Diagnostic> {
    parse_identifier(context)
}

// Parse a file:
//      File =
//          (<Attributes> (<AddressBlock> | <Module> | <Script>))*
fn parse(context: &mut Context) -> Result<Vec<ParseTree>, Diagnostic> {
    let mut trees = vec![];
    // Advance begin of file
    context.tokens.advance()?;
    while context.tokens.peek() != Tok::EOF {
        trees.push(parse_tree(context)?)
    }
    // Advance end of file
    context.tokens.advance()?;
    Ok(trees)
}

fn parse_tree(context: &mut Context) -> Result<ParseTree, Diagnostic> {
    let tok = context.tokens.peek();
    match tok {
        Tok::Module => parse_module(context),
        Tok::Script => parse_script(context),

        Tok::Fun => parse_function(vec![], context),
        Tok::Struct => parse_struct(vec![], context),
        Tok::NumSign => parse_attributes(context),
        Tok::Use => parse_use(context),
        Tok::Public | Tok::Native => parse_modifier_follow(context),

        Tok::Friend => parse_friend(context),
        Tok::Let => parse_let(context),
        Tok::Const => parse_constant(context),

        Tok::Spec => parse_spec(context),

        Tok::Invariant => parse_invariant(context),

        Tok::Identifier => match context.tokens.content() {
            //   Spec Member
            "assert" => parse_single_condition(context, SingleSpecCondition::Assert),
            "assume" => parse_single_condition(context, SingleSpecCondition::Assume),
            "ensures" => parse_single_condition(context, SingleSpecCondition::Ensures),
            "requires" => parse_single_condition(context, SingleSpecCondition::Requires),
            "decreases" => parse_single_condition(context, SingleSpecCondition::Decreases),
            "succeeds_if" => parse_single_condition(context, SingleSpecCondition::SucceedsIf),

            "aborts_with" => parse_comma_spec_condition(context, CommaSpecCondition::AbortsWith),
            "modifies" => parse_comma_spec_condition(context, CommaSpecCondition::Modifies),

            "aborts_if" => parse_abort_if(context),
            "emits" => parse_emits(context),

            "axiom" => parse_axiom(context),
            "include" => parse_spec_include(context),
            "apply" => parse_spec_apply(context),
            "pragma" => parse_spec_pragma(context),
            "global" | "local" => parse_spec_variable(context),
            "update" => parse_spec_update(context),
            //   Spec Member
            ENTRY_MODIFIER => parse_modifier_follow(context),

            "address" => parse_address_block(context),
            _ => todo!(),
        },

        _ => parse_exp_semicolon(context),
    }
}

pub fn parse_file(
    files: &mut FilesSourceText,
    fname: Symbol,
) -> anyhow::Result<(Vec<ParseTree>, Diagnostics, FileHash, Vec<Token>)> {
    let mut diags = Diagnostics::new();
    let mut f = File::open(fname.as_str())
        .map_err(|err| std::io::Error::new(err.kind(), format!("{}: {}", err, fname)))?;
    let mut source_buffer = String::new();
    f.read_to_string(&mut source_buffer)?;
    let file_hash = FileHash::new(&source_buffer);
    let buffer = match verify_string(file_hash, &source_buffer) {
        Err(ds) => {
            diags.extend(ds);
            files.insert(file_hash, (fname, source_buffer));
            return Ok((vec![], diags, file_hash, vec![]));
        }
        Ok(()) => &source_buffer,
    };
    let (defs, tokens) = match parse_file_string(file_hash, buffer) {
        Ok((defs, tokens)) => (defs, tokens),
        Err(ds) => {
            diags.extend(ds);
            (vec![], vec![])
        }
    };
    files.insert(file_hash, (fname, source_buffer));
    Ok((defs, diags, file_hash, tokens))
}

/// Parse the `input` string as a file of Move source code and return the
/// result as either a pair of FileDefinition and doc comments or some Diagnostics. The `file` name
/// is used to identify source locations in error messages.
pub fn parse_file_string(
    file_hash: FileHash,
    input: &str,
) -> Result<(Vec<ParseTree>, Vec<Token>), Diagnostics> {
    let mut tokens = FidelityLexer::new(input, file_hash);
    let mut context = Context::new(&mut tokens);
    parse(&mut context)
        .map_err(|e| Diagnostics::from(vec![e]))
        .map(|defs| (defs, context.tokens.get_tokens()))
}
