// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use std::mem;

use crate::{
    diag,
    diagnostics::Diagnostic,
    parser::{
        lexer::{find_token, Tok},
        syntax::make_loc,
    },
};
use move_command_line_common::files::FileHash;
use move_ir_types::location::Loc;
use move_symbol_pool::Symbol;

use super::{cst::ParsedToken, token_range::TokenRange};

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Token {
    pub kind: Tok,
    pub content: Symbol,
    pub loc: Loc,
}

impl Token {
    pub fn new(kind: Tok, content: Symbol, loc: Loc) -> Self {
        Token { kind, content, loc }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct FidelityToken<'a> {
    pub token: Token,
    pub tokens: Vec<Token>,
    pub content: &'a str,
}

impl<'a> FidelityToken<'a> {
    pub fn new(token: Token, tokens: Vec<Token>, content: &'a str) -> Self {
        FidelityToken {
            token,
            tokens,
            content,
        }
    }
}

pub struct FidelityLexer<'input> {
    text: &'input str,
    file_hash: FileHash,
    cur_start: usize,
    cur_end: usize,
    prev_end: usize,
    token: FidelityToken<'input>,
    pub cached_tokens: Vec<Token>,
}

impl<'input> FidelityLexer<'input> {
    pub fn new(text: &'input str, file_hash: FileHash) -> FidelityLexer<'input> {
        FidelityLexer {
            text,
            file_hash,
            cur_start: 0,
            cur_end: 0,
            prev_end: 0,
            token: FidelityToken::new(
                Token::new(Tok::BOF, Symbol::from(""), Loc::new(file_hash, 0, 0)),
                Vec::new(),
                text,
            ),
            cached_tokens: vec![],
        }
    }

    pub fn get_tokens(&mut self) -> Vec<Token> {
        mem::take(&mut self.cached_tokens)
    }

    pub fn peek_fadelity(&self) -> &FidelityToken {
        &self.token
    }

    pub fn current_token(&self) -> Token {
        self.token.token
    }
    pub fn token_range(&self, start: usize, end: usize) -> TokenRange {
        TokenRange::new(start, end)
    }

    pub fn peek(&self) -> Tok {
        self.token.token.kind
    }

    pub fn content(&self) -> &str {
        &self.token.token.content.as_str()
    }

    pub fn tokens(&self) -> &[Token] {
        &self.cached_tokens
    }

    pub fn tokens_loc(&self) -> usize {
        self.cached_tokens.len()
    }

    pub fn file_hash(&self) -> FileHash {
        self.file_hash
    }

    pub fn start_loc(&self) -> usize {
        self.cur_start
    }

    pub fn previous_end_loc(&self) -> usize {
        self.prev_end
    }

    pub fn current_loc(&self) -> Loc {
        self.token.token.loc
    }
    pub fn lookahead(&self) -> Result<Tok, Diagnostic> {
        let text = &self.text[self.cur_end..];
        Ok(find_fidelity_token(self.file_hash, text, self.cur_end)?
            .0
            .token
            .kind)
    }

    pub fn lookahead2(&self) -> Result<(Tok, Tok), Diagnostic> {
        let text = &self.text[self.cur_end..];
        let (tok1, len) = find_fidelity_token(self.file_hash, text, self.cur_end)?;
        let text2 = &self.text[self.cur_end + len..];
        let (tok2, _) = find_fidelity_token(self.file_hash, text2, self.cur_end + len)?;
        Ok((tok1.token.kind, tok2.token.kind))
    }

    pub fn advance(&mut self) -> Result<ParsedToken, Diagnostic> {
        let start_token_index = self.tokens_loc();
        let pre_token = self.current_token();
        self.cached_tokens.append(&mut self.token.tokens);
        self.prev_end = self.token.token.loc.end() as usize;
        self.cur_start = self.cur_end;
        let text = &self.text[self.cur_start..];
        let (token, len) = find_fidelity_token(self.file_hash, text, self.cur_start)?;
        self.cur_end = self.cur_start + len;
        self.token = token;
        let end_token_index = self.tokens_loc();
        let parsed_token = ParsedToken::new(
            pre_token,
            self.token_range(start_token_index, end_token_index),
        );
        Ok(parsed_token)
    }

    pub fn match_token(&mut self, tok: Tok) -> Result<bool, Diagnostic> {
        if self.peek() == tok {
            self.advance()?;
            Ok(true)
        } else {
            Ok(false)
        }
    }


    pub fn consume_token(&mut self, tok: Tok) -> Result<ParsedToken, Diagnostic> {
        self.consume_token_(tok, self.start_loc(), "")
    }

    pub fn consume_token_(
        &mut self,
        tok: Tok,
        expected_start_loc: usize,
        expected_case: &str,
    ) -> Result<ParsedToken, Diagnostic> {
        if self.peek() == tok {
            self.advance()
        } else {
            let expected = format!("'{}'{}", tok, expected_case);
            Err(self.unexpected_token_error_(expected_start_loc, &expected))
        }
    }
    fn current_token_error_string(&self) -> String {
        if self.peek() == Tok::EOF {
            "end-of-file".to_string()
        } else {
            format!("'{}'", self.content())
        }
    }

    pub fn unexpected_token_error(&self, expected: &str) -> Diagnostic {
        self.unexpected_token_error_(self.start_loc(), expected)
    }

    fn current_token_loc(&self) -> Loc {
        self.token.token.loc
    }

    fn unexpected_token_error_(&self, expected_start_loc: usize, expected: &str) -> Diagnostic {
        let unexpected_loc = self.current_token_loc();
        let unexpected = self.current_token_error_string();
        let expected_loc = if expected_start_loc < self.start_loc() {
            make_loc(
                self.file_hash(),
                expected_start_loc,
                self.previous_end_loc(),
            )
        } else {
            unexpected_loc
        };
        diag!(
            Syntax::UnexpectedToken,
            (unexpected_loc, format!("Unexpected {}", unexpected)),
            (expected_loc, format!("Expected {}", expected)),
        )
    }

    // Replace the current token. The lexer will always match the longest token,
    // but sometimes the parser will prefer to replace it with a shorter one,
    // e.g., ">" instead of ">>".
    pub fn adjust_token(&mut self, end_token: Tok) {
        if self.peek() == Tok::GreaterGreater && end_token == Tok::Greater {
            let token = Token::new(
                Tok::Greater,
                Symbol::from(">"),
                Loc::new(
                    self.file_hash,
                    self.cur_start as u32,
                    (self.cur_start + 1) as u32,
                ),
            );
            self.token = FidelityToken::new(
                token,
                vec![token],
                &self.text[self.cur_start..self.cur_start + 1],
            );
            self.cur_end = self.cur_start + 1
        }
    }
}

pub fn find_fidelity_token(
    file_hash: FileHash,
    text: &str,
    start_offset: usize,
) -> Result<(FidelityToken, usize), Diagnostic> {
    let mut cur_text = text;
    let mut text_len = 0;
    let mut new_tokens: Vec<Token> = Vec::new();
    let mut non_comment_token: Option<Token> = None;
    let mut cur_offset = start_offset;
    loop {
        let (tok, length) = find_token(file_hash, cur_text, cur_offset)?;
        let range = Loc::new(file_hash, cur_offset as u32, (cur_offset + length) as u32);
        let content = Symbol::from(&cur_text[..length]);
        let new_token = Token::new(tok, content, range);
        match tok {
            Tok::Comment(_) => {
                new_tokens.push(new_token);

                cur_offset += length;
                text_len += length;
                cur_text = &cur_text[length..];
            }
            Tok::LF => {
                new_tokens.push(new_token);
                cur_offset += length;
                text_len += length;
                cur_text = &cur_text[length..];

                if non_comment_token.is_some() {
                    break;
                }
            }
            Tok::Space | Tok::Tab | Tok::CR => {
                new_tokens.push(new_token);
                cur_offset += length;
                text_len += length;
                cur_text = &cur_text[length..];
            }
            Tok::EOF => {
                if non_comment_token.is_some() {
                    break;
                } else {
                    new_tokens.push(new_token);
                    non_comment_token = Some(new_token);
                }
            }
            _ => {
                if non_comment_token.is_none() {
                    new_tokens.push(new_token);
                    non_comment_token = Some(new_token);
                    cur_offset += length;
                    text_len += length;
                    cur_text = &cur_text[length..];
                } else {
                    break;
                }
            }
        }
    }
    non_comment_token
        .map(|_| {
            (
                FidelityToken::new(non_comment_token.unwrap(), new_tokens, &text[0..text_len]),
                text_len,
            )
        })
        .ok_or_else(|| {
            diag!(
                Bug::TokenizedFailure,
                (
                    Loc::new(file_hash, start_offset as u32, cur_offset as u32),
                    "Could not find valid token."
                )
            )
        })
}

#[cfg(test)]
mod test {

    use move_command_line_common::files::FileHash;
    use move_ir_types::location::Loc;
    use move_symbol_pool::Symbol;

    use crate::parser::{comments::CommentKind, lexer::Tok};

    use super::{find_fidelity_token, FidelityLexer, FidelityToken, Token};

    #[test]
    fn test_find_fidelity_token_trailing_comment() {
        let file_hash = FileHash::empty();
        let text = "ident /*comment*/ ,";
        let (token, length) = find_fidelity_token(file_hash, text, 0).unwrap();

        let expected_tokens = vec![
            Token::new(
                Tok::Identifier,
                Symbol::from("ident"),
                Loc::new(file_hash, 0, 5),
            ),
            Token::new(Tok::Space, Symbol::from(" "), Loc::new(file_hash, 5, 6)),
            Token::new(
                Tok::Comment(CommentKind::BlockComment),
                Symbol::from("/*comment*/"),
                Loc::new(file_hash, 6, 17),
            ),
            Token::new(Tok::Space, Symbol::from(" "), Loc::new(file_hash, 17, 18)),
        ];

        let expected = FidelityToken::new(
            Token::new(
                Tok::Identifier,
                Symbol::from("ident"),
                Loc::new(file_hash, 0, 5),
            ),
            expected_tokens,
            "ident /*comment*/ ",
        );
        assert_eq!(token, expected);
        assert_eq!(length, 18)
    }

    #[test]
    fn test_find_fidelity_token_leading_comment() {
        let file_hash = FileHash::empty();
        let text = "//comment\n ident ,";
        let (token, length) = find_fidelity_token(file_hash, text, 0).unwrap();

        let expected_tokens = vec![
            Token::new(
                Tok::Comment(CommentKind::SignleLine),
                Symbol::from("//comment"),
                Loc::new(file_hash, 0, 9),
            ),
            Token::new(Tok::LF, Symbol::from("\n"), Loc::new(file_hash, 9, 10)),
            Token::new(Tok::Space, Symbol::from(" "), Loc::new(file_hash, 10, 11)),
            Token::new(
                Tok::Identifier,
                Symbol::from("ident"),
                Loc::new(file_hash, 11, 16),
            ),
            Token::new(Tok::Space, Symbol::from(" "), Loc::new(file_hash, 16, 17)),
        ];

        let expected = FidelityToken::new(
            Token::new(
                Tok::Identifier,
                Symbol::from("ident"),
                Loc::new(file_hash, 11, 16),
            ),
            expected_tokens,
            "//comment\n ident ",
        );
        assert_eq!(token, expected);
        assert_eq!(length, 17)
    }

    #[test]
    fn test_find_fidelity_token_eof() {
        let file_hash = FileHash::empty();
        let text = "//comment\n ";
        let (token, length) = find_fidelity_token(file_hash, text, 0).unwrap();

        let expected_tokens = vec![
            Token::new(
                Tok::Comment(CommentKind::SignleLine),
                Symbol::from("//comment"),
                Loc::new(file_hash, 0, 9),
            ),
            Token::new(Tok::LF, Symbol::from("\n"), Loc::new(file_hash, 9, 10)),
            Token::new(Tok::Space, Symbol::from(" "), Loc::new(file_hash, 10, 11)),
            Token::new(Tok::EOF, Symbol::from(""), Loc::new(file_hash, 11, 11)),
        ];

        let expected = FidelityToken::new(
            Token::new(Tok::EOF, Symbol::from(""), Loc::new(file_hash, 11, 11)),
            expected_tokens,
            "//comment\n ",
        );
        assert_eq!(token, expected);
        assert_eq!(length, 11)
    }

    #[test]

    fn test_lexer() {
        let mut lexer = FidelityLexer::new("hello you are great", FileHash::empty());

        let _ = lexer.advance();
        assert_eq!(
            lexer.token,
            FidelityToken::new(
                Token::new(
                    Tok::Identifier,
                    Symbol::from("hello"),
                    Loc::new(FileHash::empty(), 0, 5)
                ),
                vec![
                    Token::new(
                        Tok::Identifier,
                        Symbol::from("hello"),
                        Loc::new(FileHash::empty(), 0, 5)
                    ),
                    Token::new(
                        Tok::Space,
                        Symbol::from(" "),
                        Loc::new(FileHash::empty(), 5, 6)
                    ),
                ],
                "hello "
            )
        );

        let _ = lexer.advance();
        assert_eq!(
            lexer.token,
            FidelityToken::new(
                Token::new(
                    Tok::Identifier,
                    Symbol::from("you"),
                    Loc::new(FileHash::empty(), 6, 9)
                ),
                vec![
                    Token::new(
                        Tok::Identifier,
                        Symbol::from("you"),
                        Loc::new(FileHash::empty(), 6, 9)
                    ),
                    Token::new(
                        Tok::Space,
                        Symbol::from(" "),
                        Loc::new(FileHash::empty(), 9, 10)
                    ),
                ],
                "you "
            )
        )
    }
}
