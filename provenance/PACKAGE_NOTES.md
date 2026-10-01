# Source scope and verification

This repository contains the 565-module local import closure of `Schubert.RS.Audit`. All local
imports are included. It consists of 474 modules under `Schubert/RS/`, the generated entry
modules `Schubert.RS.Main` and `Schubert.RS.Audit`, 37 modules of the library `Schubert/GLRep/`
(polynomial and rational representations of general linear groups and their Levi subgroups), 26
modules of the library `Schubert/LinearProgramming/` (polynomial-time feasibility of systems of
linear inequalities), 12 modules of the library `Schubert/QuiverInvariants/` (semi-invariants
of quivers and the saturation property), and 14 prerequisite modules under `Schubert/Algebra/`
and `Schubert/TypeA/` that were already part of release 1.0.0. Each of these libraries proves
one of the statements of `Schubert/RS/Statements/` (see `docs/STATEMENTS.md`); their modules
are included as far as the endpoints import them. The 197 complexitylib files imported by this
closure are vendored under `vendor/complexitylib/` (see `THIRD_PARTY_NOTICES.md`). Mathlib
(`b2bf051`) and Tau Ceti (`48fe7a5`) are pinned public Lake dependencies and are not included.

## Source preparation

The sources are those of the development tree, unchanged. No module or identifier
was renamed for this release; the renamings made when release 1.0.0 was prepared
are recorded in that release. `LOCAL_MODULES.json` records, for every module, the
path and hash in this release, with `origin_kind` `unchanged` (563)
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
