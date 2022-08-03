// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use move_ir_types::location::Loc;

use super::lexer::Token;

#[derive(Debug, Copy, Clone, PartialEq)]
pub struct TokenRange {
    pub start: usize,
    pub end: usize,
}

impl Default for TokenRange {
    fn default() -> Self {
        Self { start: 0, end: 0 }
    }
}

impl TokenRange {
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    pub fn loc(&self, tokens: &[Token]) -> Loc {
        make_loc(tokens[self.start].loc, tokens[self.end].loc)
    }
}

fn make_loc(start: Loc, end: Loc) -> Loc {
    Loc::new(start.file_hash(), start.start(), end.end())
}
