# Source scope and verification

This repository contains the 1303-module local import closure of `Schubert.RS.Audit`. All local
imports are included. It consists of 479 modules under `Schubert/RS/`, the generated entry
modules `Schubert.RS.Main` and `Schubert.RS.Audit`, 26 modules of the library
`Schubert/LinearProgramming/` (polynomial-time feasibility of systems of linear inequalities),
12 modules of the library `Schubert/QuiverInvariants/` (semi-invariants of quivers and the
saturation property), 413 modules of `Schubert/FlagVarieties/` (the flag scheme over a
commutative ring, Schubert, opposite Schubert and Richardson varieties, line bundles and their
sections, and the representations of the Borel subgroup on them), 285 modules of
`Schubert/Demazure/` (flag minors, Demazure modules, keys and atoms), 66 modules of
`Schubert/GLRep/` (polynomial and rational representations of general linear groups, their Levi
subgroups and their Borel subgroups), 20 modules of `Schubert/TypeA/` (permutations, the Bruhat
order and divided differences). Each of the libraries `Schubert/GLRep/`,
`Schubert/LinearProgramming/`, `Schubert/QuiverInvariants/` proves one of the statements of
`Schubert/RS/Statements/` (see `docs/STATEMENTS.md`). The modules of
`Schubert/LinearProgramming/`, `Schubert/QuiverInvariants/` are included as far as the
endpoints import them. The folders `Schubert/FlagVarieties/`, `Schubert/Demazure/`,
`Schubert/GLRep/`, `Schubert/TypeA/` form the flag-variety module, version 0.1.0, which is
included complete: `FLAG_MODULE_MANIFEST.json` lists each of its 785 files with its SHA-256
hash. The module imports only Mathlib, Tau Ceti and itself; the sheaf-theoretic form of
Corollary 1.2 (`Schubert/RS/Geometric/`) is built on it. The 197 complexitylib files imported
by this closure are vendored under `vendor/complexitylib/` (see `THIRD_PARTY_NOTICES.md`).
Mathlib (`b2bf051`) and Tau Ceti (`48fe7a5`) are pinned public Lake dependencies and are not
included.

## Source preparation

The sources are those of the development tree, unchanged. No module or identifier
was renamed for this release; the renamings made when release 1.0.0 was prepared
are recorded in that release. `LOCAL_MODULES.json` records, for every module, the
path and hash in this release, with `origin_kind` `unchanged` (1301)
or `generated` (2).

`Schubert.RS.Main` imports the Lean counterparts of the labelled statements of the paper
(listed in `docs/STATEMENTS.md`) and the endpoint modules; `Schubert.RS.Audit` prints the
signatures of the main declarations and their axioms. Both are generated for this
release.

Development records, development audit modules, unrelated library developments
and compiled local proof files are not part of the source release.

## Build and axiom checks

`BUILD_CHECK.json` records the build of the prepared Lean sources with `build.py`:
Lake first builds the Tau Ceti modules imported by the local files and the vendored
complexitylib files (Mathlib objects come from the public Mathlib cache), then
`build.py` compiles all local modules from the distributed sources.
`ENDPOINT_AUDIT.txt` contains the output of the audit module: signatures, including
hypotheses, and transitive axioms.

`SHA256SUMS.json` covers every distributed file except itself. The verification
helper checks these hashes, that all local and vendored imports are present, that
the Lake requirements match `lake-manifest.json`, and that the vendored complexitylib
files match their recorded upstream hashes.
