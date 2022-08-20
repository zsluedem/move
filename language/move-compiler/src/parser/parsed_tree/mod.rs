// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashMap;

use crate::{
    diagnostics::{codes::Severity, Diagnostics, FilesSourceText},
    parser::ensure_targets_deps_dont_intersect,
    shared::{CompilationEnv, IndexedPackagePath},
};

use self::syntax::parse_file;

use super::{
    cst::{self, PackageDefinition, Program},
    find_move_filenames_with_address_mapping,
};

pub mod lexer;
pub mod syntax;
pub mod token_range;

pub fn parse_program(
    compilation_env: &mut CompilationEnv,
    targets: Vec<IndexedPackagePath>,
    deps: Vec<IndexedPackagePath>,
) -> anyhow::Result<(FilesSourceText, Result<cst::Program, Diagnostics>)> {
    let targets = find_move_filenames_with_address_mapping(targets)?;
    let mut deps = find_move_filenames_with_address_mapping(deps)?;
    ensure_targets_deps_dont_intersect(compilation_env, &targets, &mut deps)?;
    let mut files: FilesSourceText = HashMap::new();
    let mut source_definitions = Vec::new();
    let mut lib_definitions = Vec::new();
    let mut diags: Diagnostics = Diagnostics::new();

    for IndexedPackagePath {
        package,
        path,
        named_address_map,
    } in targets
    {
        let (source_trees, ds, file_hash, source_tokens) = parse_file(&mut files, path)?;
        source_definitions.push(PackageDefinition {
            package,
            named_address_map,
            source_trees,
            source_tokens,
            file_hash,
        });
        diags.extend(ds);
    }

    for IndexedPackagePath {
        package,
        path,
        named_address_map,
    } in deps
    {
        let (source_trees, ds, file_hash, source_tokens) = parse_file(&mut files, path)?;
        lib_definitions.push(PackageDefinition {
            package,
            named_address_map,
            source_trees,
            source_tokens,
            file_hash,
        });
        diags.extend(ds);
    }

    // TODO fix this so it works likes other passes and the handling of errors is done outside of
    // this function
    let env_result = compilation_env.check_diags_at_or_above_severity(Severity::BlockingError);
    if let Err(env_diags) = env_result {
        diags.extend(env_diags)
    }

    let res = if diags.is_empty() {
        let pprog = Program {
            source_definitions,
            lib_definitions,
        };
        Ok(pprog)
    } else {
        Err(diags)
    };
    Ok((files, res))
}
