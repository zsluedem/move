// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use move_command_line_common::files::FileHash;
use move_ir_types::location::Loc;
use move_symbol_pool::Symbol;

use super::{lexer::Token, token_range::TokenRange};
use crate::{
    parser::{
        ast::{BinOp_, QuantKind_},
        comments::Comment,
        lexer::Tok,
    },
    shared::{NamedAddressMapIndex},
};

#[derive(Debug, Clone)]
pub struct Program {
    pub source_definitions: Vec<PackageDefinition>,
    pub lib_definitions: Vec<PackageDefinition>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Definition {
    Module(Module),
    Address(Address),
    Script(Script),
}
#[derive(Debug, Clone)]
pub struct PackageDefinition {
    pub package: Option<Symbol>,
    pub named_address_map: NamedAddressMapIndex,
    pub source_trees: Vec<Definition>,
    pub source_tokens: Vec<Token>,
    pub file_hash: FileHash,
}

#[derive(Debug, Clone, PartialEq)]
pub struct SpannedWithComment<T> {
    pub value: T,
    pub token_range: TokenRange,
}

impl<T> SpannedWithComment<T> {
    pub fn new(value: T, token_range: TokenRange) -> Self {
        SpannedWithComment { value, token_range }
    }

    pub fn loc(&self, tokens: &[Token]) -> Loc {
        self.token_range.loc(tokens)
    }

    pub fn value(&self) -> &T {
        &self.value
    }

    fn is_comment_spaces(token: Tok) -> bool {
        matches!(
            token,
            Tok::Comment(_) | Tok::Space | Tok::Tab | Tok::LF | Tok::CR
        )
    }

    fn find_comments(tokens: &[Token]) -> Vec<Comment> {
        tokens
            .iter()
            .filter_map(|t| match t.kind {
                Tok::Comment(kind) => Some(Comment::new(kind, t.content, t.loc)),
                _ => None,
            })
            .collect::<Vec<_>>()
    }

    pub fn trailing_comments(&self, source_tokens: &[Token]) -> Vec<Comment> {
        let end_pos = source_tokens[self.token_range.start..self.token_range.end]
            .iter()
            .rev()
            .position(|t| !Self::is_comment_spaces(t.kind));
        match end_pos {
            Some(end) => {
                let trailing_tokens =
                    &source_tokens[self.token_range.end - end..self.token_range.end];
                Self::find_comments(trailing_tokens)
            }
            None => vec![],
        }
    }

    pub fn leading_comments(&self, source_tokens: &[Token]) -> Vec<Comment> {
        let end_pos = source_tokens[self.token_range.start..self.token_range.end]
            .iter()
            .position(|t| !Self::is_comment_spaces(t.kind));
        match end_pos {
            Some(end) => {
                let trailing_tokens =
                    &source_tokens[self.token_range.start..self.token_range.start + end];
                Self::find_comments(trailing_tokens)
            }
            None => vec![],
        }
    }
}

pub type ParsedToken = SpannedWithComment<Token>;

pub type Name = ParsedToken;

pub type Attribute = SpannedWithComment<Attribute_>;
pub type Attributes = SpannedWithComment<Vec<Attribute>>;
pub type Ability = ParsedToken;
pub type Var = ParsedToken;
pub type Field = ParsedToken;
pub type Op = ParsedToken;

// (<Name>|<Num>)::<Name>::<Name>
pub type NameAccessChain = SpannedWithComment<Vec<Name>>;
pub type LeadingNameAccess = Name;
pub type SpecApplyFragment = ParsedToken;

pub type QuantKind = SpannedWithComment<QuantKind_>;
pub type BinOp = SpannedWithComment<BinOp_>;
pub type UnaryOp = SpannedWithComment<UnaryOp_>;

#[derive(Debug, Clone, PartialEq)]
pub enum ParsedTree {
    Function(Function),
    Struct(Struct),
    Sequence(SequenceItem),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Script_ {
    pub attributes: Vec<Attributes>,
    pub members: Vec<ParsedTree>,
}

pub type Script = SpannedWithComment<Script_>;

#[derive(Debug, Clone, PartialEq)]
pub struct Module_ {
    pub attributes: Vec<Attributes>,
    pub address: Option<Name>,
    pub name: Name,
    pub body: Vec<ParsedTree>,
    pub is_spec_mod: bool,
}

pub type Module = SpannedWithComment<Module_>;

#[derive(Debug, Clone, PartialEq)]
pub struct Address_ {
    pub attributes: Vec<Attributes>,
    pub address: LeadingNameAccess,
    pub modules: Vec<Module>,
}
pub type Address = SpannedWithComment<Address_>;

#[derive(Debug, Clone, PartialEq)]
pub struct Function_ {
    pub attributes: Vec<Attributes>,
    pub modifiers: Modifiers,
    pub signatures: FunctionSignature,
    pub acquires: Vec<NameAccessChain>,
    pub name: Name,
    pub body: FunctionBody,
}

pub type Function = SpannedWithComment<Function_>;

#[derive(Debug, Clone, PartialEq)]
pub struct Struct_ {
    pub attributes: Vec<Attributes>,
    pub modifiers: Modifiers,
    pub abilities: Vec<Ability>,
    pub name: Name,
    pub type_parameters: Vec<StructTypeParameter>,
    pub fields: StructFields,
}

pub type Struct = SpannedWithComment<Struct_>;

#[derive(Debug, Clone, PartialEq)]
pub struct SpecBlock_ {
    pub attributes: Vec<Attributes>,
    pub target: SpecBlockTarget,
    pub uses: Vec<UseDecl>,
    pub members: Vec<SpecBlockMember>,
}

pub type SpecBlock = SpannedWithComment<SpecBlock_>;

#[derive(Debug, Clone, PartialEq)]
pub enum SingleSpecCondition {
    Assert,
    Assume,
    Ensures,
    Requires,
    Decreases,
    SucceedsIf,
}

#[derive(Debug, Clone, PartialEq)]
pub enum CommaSpecCondition {
    AbortsWith,
    Modifies,
}

pub type SpecTypeParameters = SpannedWithComment<Vec<(Name, Vec<Ability>)>>;

#[derive(Debug, Clone, PartialEq)]
pub enum SpecConditionKind_ {
    // ("assert" | "assume" | "ensures" | "requires" | "decreases"| "succeeds_if" ) <ConditionProperties> <Exp> ";"
    SingleExpCondition {
        kind: SpannedWithComment<SingleSpecCondition>,
        properties: Vec<PragmaProperty>,
        exp: Box<Exp>,
    },
    // "aborts_if" <ConditionProperties> <Exp> ["with" <Exp>] ";"
    AbortsIf {
        loc: ParsedToken,
        properties: Vec<PragmaProperty>,
        exp: Box<Exp>,
        with_exp: Option<Box<Exp>>,
    },
    //  "aborts_with" | "modifies" <ConditionProperties> [Comma <Exp>]* ";"
    CommaExpCondition {
        kind: SpannedWithComment<CommaSpecCondition>,
        properties: Vec<PragmaProperty>,
        exps: Vec<Exp>,
    },
    //  "emits" <ConditionProperties> <Exp> "to" <Exp> [If <Exp>] ";"
    Emits {
        loc: ParsedToken,
        properties: Vec<PragmaProperty>,
        exp: Box<Exp>,
        to_exp: Box<Exp>,
        if_exp: Option<Box<Exp>>,
    },
    // "invariant" <OptionalTypeParameters> [ "update" ] <ConditionProperties> <Exp> ";"
    Invariant {
        types: SpecTypeParameters,
        properties: Vec<PragmaProperty>,
        exp: Box<Exp>,
    },
    InvariantUpdate {
        types: SpecTypeParameters,
        properties: Vec<PragmaProperty>,
        exp: Box<Exp>,
    },
    // "axiom" <OptionalTypeParameters> <ConditionProperties> <Exp> ";"
    Axiom {
        types: SpecTypeParameters,
        properties: Vec<PragmaProperty>,
        exp: Box<Exp>,
    },
}

pub type SpecConditionKind = SpannedWithComment<SpecConditionKind_>;

#[derive(Debug, Clone, PartialEq)]
pub enum SequenceItem_ {
    UseDecl(UseDecl),
    FriendDecl(FriendDecl),
    // let b;
    Declare(LetDeclare),
    // let b : t = e;
    // let b = e;
    Bind(LetAssign),
    Constant(ConstantDecl),
    // e
    // e;
    Exp(Exp, SemicolonEnd),
    // spec {}
    Spec(SpecBlock),
}

#[derive(Debug, Clone, PartialEq)]
pub struct LetDeclare_ {
    pub var: BindList,
    pub type_: Option<Type>,
}
pub type LetDeclare = SpannedWithComment<LetDeclare_>;

#[derive(Debug, Clone, PartialEq)]
pub struct LetAssign_ {
    pub var: BindList,
    pub type_: Option<Type>,
    pub exp: Exp,
}
pub type LetAssign = SpannedWithComment<LetAssign_>;

#[derive(Debug, Clone, PartialEq)]
pub struct FriendDecl {
    pub attributes: Vec<Attributes>,
    pub friend: NameAccessChain,
}

#[derive(Debug, Clone, PartialEq)]
pub enum SemicolonEnd {
    IsSemicolonEnd(Token),
    NotSemicolonEnd,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Constant_ {
    pub signature: Type,
    pub name: Name,
    pub exp: Exp,
}

pub type Constant = SpannedWithComment<Constant_>;

#[derive(Debug, Clone, PartialEq)]
pub struct ConstantDecl {
    pub attributes: Vec<Attributes>,
    pub constant: Constant,
}

pub type SequenceItem = SpannedWithComment<SequenceItem_>;

pub type Block = Vec<SequenceItem>;

#[derive(Debug, Clone, PartialEq)]
pub enum SpecBlockMember_ {
    Condition(Box<SpecConditionKind>),
    Function {
        uninterpreted: bool,
        name: Name,
        signature: FunctionSignature,
        body: FunctionBody,
    },
    Variable {
        is_global: bool,
        name: Name,
        type_parameters: Vec<(Name, Vec<Ability>)>,
        type_: Type,
        init: Option<Exp>,
    },
    Let {
        name: Name,
        post_state: bool,
        def: Exp,
    },
    Update {
        lhs: Exp,
        rhs: Exp,
    },
    Include {
        properties: Vec<PragmaProperty>,
        exp: Exp,
    },
    Apply {
        exp: Exp,
        patterns: Vec<SpecApplyPattern>,
        exclusion_patterns: Vec<SpecApplyPattern>,
    },
    Pragma {
        properties: Vec<PragmaProperty>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct PragmaProperty_ {
    pub name: ParsedToken,
    pub value: Option<PragmaValue>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum PragmaValue {
    Literal(Value),
    Ident(NameAccessChain),
}
pub type PragmaProperty = SpannedWithComment<PragmaProperty_>;

pub type SpecBlockMember = SpannedWithComment<SpecBlockMember_>;

#[derive(Debug, Clone, PartialEq)]
pub struct SpecApplyPattern_ {
    pub visibility: Option<Visibility>,
    pub name_pattern: Vec<Name>,
    pub type_parameters: Vec<(Name, Vec<Ability>)>,
}
pub type SpecApplyPattern = SpannedWithComment<SpecApplyPattern_>;

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionBody_ {
    pub body: Block,
    pub is_native: bool,
}

pub type FunctionBody = SpannedWithComment<FunctionBody_>;

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum UnaryOp_ {
    // !
    Not,
    // &UnaryOp_
    Borrow,
    // &mut
    BorrowMut,
    // *
    Dereference,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Exp_ {
    Value(Value),
    // [m::]n[<t1, .., tn>]
    Name(NameAccessChain, Option<Vec<Type>>),
    // move(x)
    Move(Var),
    // copy(x)
    Copy(Var),
    // f(earg,*)
    // f!(earg,*)
    Call(
        NameAccessChain,
        bool,
        Option<Vec<Type>>,
        SpannedWithComment<Vec<Exp>>,
    ),

    // tn {f1: e1, ... , f_n: e_n }
    Pack(
        NameAccessChain,
        Option<Vec<Type>>,
        Vec<(Field, Option<Exp>)>,
    ),

    // vector [ e1, ..., e_n ]
    // vector<t> [e1, ..., en ]
    Vector(Name, Option<Vec<Type>>, SpannedWithComment<Vec<Exp>>),

    // if (eb) et else ef
    IfElse(Box<Exp>, Box<Exp>, Option<Box<Exp>>),
    // while (eb) eloop (spec)
    While(Box<Exp>, Box<Exp>, Option<SpecBlock>),
    // loop eloop
    Loop(Box<Exp>),

    // { seq }
    Block(Block),
    // fun (x1, ..., xn) e
    Lambda(BindList, Box<Exp>), // spec only
    // forall/exists x1 : e1, ..., xn [{ t1, .., tk } *] [where cond]: en.
    Quant(
        QuantKind,
        BindWithRangeList,
        Vec<Vec<Exp>>,
        Option<Box<Exp>>,
        Box<Exp>,
    ), // spec only
    // (e1, ..., en)
    ExpList(Vec<Exp>),
    // ()
    Unit,

    // a = e
    Assign(Box<Exp>, Box<Exp>),

    // return e
    Return(Option<Box<Exp>>),
    // abort e
    Abort(Box<Exp>),
    // break
    Break,
    // continue
    Continue,

    // op e
    UnaryExp(UnaryOp, Box<Exp>),
    // e1 op e2
    BinopExp(Box<Exp>, BinOp, Box<Exp>),

    // e.f
    Dot(Box<Exp>, Name),
    // e[e']
    Index(Box<Exp>, Box<Exp>), // spec only

    // (e as t)
    Cast(Box<Exp>, Type),
    // (e: t)
    Annotate(Box<Exp>, Type),

    // Internal node marking an error was added to the error list
    // This is here so the pass can continue even when an error is hit
    UnresolvedError,
}

pub type Exp = SpannedWithComment<Exp_>;

#[derive(Debug, Clone, PartialEq)]
pub enum Value_ {
    // @<num>
    Address(ParsedToken),
    // bool, x"[0..9A..F]+",
    // b"(<ascii> | \n | \r | \t | \\ | \0 | \" | \x[0..9A..F][0..9A..F])+"
    // <num>
    Literal(Token),
}
pub type Value = SpannedWithComment<Value_>;

#[derive(Debug, Clone, PartialEq)]
pub enum Bind_ {
    Var(Var),
    Unpack(
        Box<NameAccessChain>,
        Option<Vec<Type>>,
        Vec<(Field, Option<Bind>)>,
    ),
}

pub type Bind = SpannedWithComment<Bind_>;

pub type BindList = SpannedWithComment<Vec<Bind>>;

pub type BindWithRange = SpannedWithComment<QuantBind>;
pub type BindWithRangeList = SpannedWithComment<Vec<BindWithRange>>;
#[derive(Debug, Clone, PartialEq)]
pub enum SpecBlockTarget_ {
    Code,
    Module,
    Member(Name, Option<Box<FunctionSignature>>),
    Schema(Name, Vec<(Name, Vec<Ability>)>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum QuantBind {
    // ident:type
    TypeBind(Var, Type),
    // i in Exp
    InBind(Var, Exp),
}

#[derive(Debug, Clone, PartialEq)]
pub struct ModuleIdent {
    pub address: LeadingNameAccess,
    pub module: Name,
}

pub type SpecBlockTarget = SpannedWithComment<SpecBlockTarget_>;

#[derive(Debug, Clone, PartialEq)]
pub enum Use {
    Module(ModuleIdent, Option<Name>),
    Members(ModuleIdent, Vec<(Name, Option<Name>)>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct UseDecl {
    pub attributes: Vec<Attributes>,
    pub use_: Use,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StructFields {
    pub members: Vec<(Field, Type)>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionSignature {
    pub type_parameters: Vec<(Name, Vec<Ability>)>,
    pub parameters: Vec<(Var, Type)>,
    pub return_type: Option<Type>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StructTypeParameter {
    pub is_phantom: bool,
    pub name: Name,
    pub constraints: Vec<Ability>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Type_ {
    // N
    // N<t1, ... , tn>
    Apply(NameAccessChain, Vec<Type>),
    // &t
    // &mut t
    Ref(bool, Box<Type>),
    // (t1,...,tn):t
    Fun(Vec<Type>, Box<Type>),
    // ()
    // (t1, t2, ... , tn)
    // Used for return values and expression blocks
    Sequance(Vec<Type>),
}

pub type Type = SpannedWithComment<Type_>;

#[derive(Debug, Clone, PartialEq)]
pub enum AttributeValue {
    Value(Value),
    ModuleAccess(NameAccessChain),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Attribute_ {
    Name(ParsedToken),
    Assigned(ParsedToken, AttributeValue),
    Parameterized(ParsedToken, Attributes),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Visibility_ {
    Public,
    Script,
    Friend,
    Internal,
}

pub type Visibility = SpannedWithComment<Visibility_>;

#[derive(Debug, Clone, PartialEq)]
pub enum Modifier_ {
    Visibility(Visibility),
    Native,
    Entry,
}

pub type Modifier = SpannedWithComment<Modifier_>;
pub type Modifiers = Vec<Modifier>;
