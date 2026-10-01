# Third-party material

## Cauchy–Binet lemmas

- File: `Schubert/RS/JosephPolo/GrinbergCauchyBinet.lean`
- Copyright: Meta Platforms, Inc. and affiliates.
- Source: [facebookresearch/algebraic-combinatorics](https://github.com/facebookresearch/algebraic-combinatorics),
  commit `b6022318e986a0c20764569208ba8ebbe1c04dbf`,
  `AlgebraicCombinatorics/CauchyBinet.lean`, rectangular Cauchy–Binet section.
- License: Creative Commons Attribution–NonCommercial 4.0 International
  (CC BY-NC 4.0), reproduced in
  [Grinberg.LICENSE](Schubert/RS/JosephPolo/Grinberg.LICENSE).
- Adaptations recorded in the source: narrower imports, a separate namespace,
  and Lean compatibility. The publication namespace is
  `Schubert.RS.GrinbergCauchyBinet`.

The source attribution and license text are preserved. This file is not covered
by the Apache License.

## complexitylib (vendored)

- Files: 197 Lean sources under `vendor/complexitylib/Complexitylib/`.
- Source: [SamuelSchlesinger/complexitylib](https://github.com/SamuelSchlesinger/complexitylib), commit `d29dc5d8d97de36b7425ded7fd046931a4b6d9fb`.
- License: Apache License 2.0, reproduced in [vendor/complexitylib/LICENSE](vendor/complexitylib/LICENSE).
- Modifications: none.
- Record: [vendor/complexitylib/UPSTREAM_SOURCES.json](vendor/complexitylib/UPSTREAM_SOURCES.json) lists each
  file with its upstream hash. `verify_bundle.py` checks them.

## Downloaded dependencies

These packages are downloaded by Lake at the revisions pinned in `lakefile.toml` and
`lake-manifest.json`. They are not included in this repository and keep their own
licenses.

- Tau Ceti: [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti), commit
  `48fe7a5f9ba49e3b1c11a72f54f665abc128b36a`.
- Mathlib: [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4), commit
  `b2bf051988bf69448bce88722cc09a05fea31662`.
- Their own dependencies, pinned in `lake-manifest.json`: plausible, LeanSearchClient, importGraph, proofwidgets, aesop, Qq, batteries, Cli.

## Project license

The rest of this repository is licensed under the Apache License 2.0; see
[LICENSE](LICENSE) and [NOTICE](NOTICE). The Cauchy–Binet file above is
excluded and remains under CC BY-NC 4.0.
