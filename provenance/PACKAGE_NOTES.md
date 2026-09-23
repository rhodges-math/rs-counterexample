# Source scope and verification

This repository contains the 365-module local import closure of
`Schubert.RS.Family.Audit`. All local imports are included.
External imports come from the pinned public Lake dependencies.

## Source preparation

This release was prepared from the standalone source archive dated
21 September 2026. Modules, declarations, and the common namespace were
renamed consistently, and comments were edited to describe their mathematical
content. The main results are in `Schubert.RS.Family.Main` under the namespace
`Schubert.RS.Family`.

The statements and proofs match the original archive after the documented
identifier and import renamings, removal of comments, and normalization of
whitespace. `RENAMINGS.json` lists those substitutions; `LOCAL_MODULES.json`
records the source paths and hashes for this release and the original archive.
The adapted Cauchy–Binet file received the same namespace change; its
copyright, source attribution, and license are retained.

## Original dependency isolation

The standalone archive narrowed imports in four prerequisite modules:

- `Schubert/TypeA/Polynomials/DividedDifferences.lean`
- `Schubert/TypeA/Permutations/NorthwestRankBounds.lean`
- `Schubert/RS/JosephPolo/BruhatLifting.lean`
- `Schubert/RS/JosephPolo/BruhatMonotonicity.lean`

Two small support modules contain the polynomial-ring abbreviation and
elementary northwest-rank definitions and lemmas needed by this import closure.
Unrelated developments, research notes, Git history, and compiled local proof
files are not part of the source release.

## Build and axiom checks

`BUILD_CHECK.json` records the build of the prepared Lean sources.
`ENDPOINT_AUDIT.txt` contains theorem signatures and transitive axiom output.
Only pinned public dependency caches are reused; no compiled local `Schubert`
module is imported from another project.

The final family results supply proofs of the Joseph–Polo presentation,
Demazure character formula, and PBW theorem. Their axiom lists contain only
`propext`, `Classical.choice`, and `Quot.sound`.

`SHA256SUMS.json` covers every distributed file except itself. The verification
helper checks these hashes and that all local imports are present.
