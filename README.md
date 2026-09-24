# Lean verification of the key-product counterexamples

This repository contains a Lean 4 formalization of **Theorem 1.1** in
Reuven Hodges, *Counterexamples to the Reiner–Shimozono conjecture and the
failure of Schubert filtrations* (2026).

It proves the coefficient formula for the full counterexample family, its
exact negativity criterion, and an explicit negative coefficient in 28
variables. It uses Lean **4.33.0** and a pinned version of **Mathlib**.

## AI assistance and verification

**I used GPT-6 Astra to help construct the Lean files.** I reviewed the
definitions, hypotheses, and theorem statements to check that they faithfully
express the intended mathematics and correspond to Theorem 1.1 in the paper.

The development was compiled with Lean, and the final theorems' axiom
dependencies were audited: they use only `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorry`-based proofs or additional unproved axioms.
The mathematical review addresses the correspondence between the formal
statements and the paper, which Lean's proof checking alone does not establish.

## Main result

For positive integers $p,q$ and an integer scale $\delta\ge p+q$, the paper
defines compositions $a,b,c$ in $4(p+q-1)$ variables and proves

$$
[\mathcal A_c](\kappa_a\kappa_b)
=\frac{p+q-1}{pq}\binom{p+q-2}{p-1}^{2}
 \bigl(2-(p-2)(q-2)\bigr).
$$

The coefficient is negative exactly when $(p-2)(q-2)>2$.
The explicit instance $p=q=4$, $\delta=8$ has coefficient **−350**.

The entry point is
[Family/Main.lean](Schubert/RS/Family/Main.lean):

```lean
import Schubert.RS.Family.Main

open Schubert.RS
open Schubert.RS.Family

#check atomCoefficient_eq
#check atomCoefficient_factorization
#check atomCoefficient_neg_iff
#check rank28_atomCoefficient
#check reiner_shimozono_false
```

These declarations are in `Schubert.RS.Family`.

| Declaration | Result |
| --- | --- |
| `atomCoefficient_eq` | The family coefficient as an integer binomial expression |
| `atomCoefficient_factorization` | The factored formula above, viewed in the rationals |
| `atomCoefficient_neg_iff` | The exact range of negative coefficients |
| `existsUnique_atomExpansion` | Existence and uniqueness of the integral atom expansion, including the specified coefficient |
| `not_atomPositive` | Failure of atom positivity in the negative range |
| `rank28_atomCoefficient` | The explicit coefficient −350 in 28 variables |
| `rank28_not_atomPositive` | The corresponding product is not atom positive |
| `reiner_shimozono_false` | The universal Reiner–Shimozono positivity assertion is false |

The family data are in [Family/Data.lean](Schubert/RS/Family/Data.lean), and the
28-variable example is in [ConcreteData.lean](Schubert/RS/ConcreteData.lean).

| Paper notation | Lean notation |
| --- | --- |
| $\delta$ | `P.K` |
| $p+q-1$ | `P.m` |
| $4(p+q-1)$ variables | `P.rank` |
| $\kappa_a$ | `key a` |
| $\mathcal A_c$ | `atom c` |
| $[\mathcal A_c]f$ | `atomCoefficient f c` |

The paper's Narayana reformulation is equivalent to the factored expression
above; this snapshot does not introduce a separate Narayana-number definition.
The later filtration and quiver-positivity results are outside this
repository's scope.

## Build and verify

Install [Lean and Lake through elan](https://lean-lang.org/install/) and
[Python 3](https://www.python.org/downloads/). Git must also be available.
The `lean-toolchain` file selects Lean 4.33.0 automatically, and
`lake-manifest.json` pins Mathlib and its public dependencies.

From the repository directory, run:

```text
lake exe cache get
python build.py --jobs 3
lake env lean Schubert/RS/Family/Audit.lean
```

On Windows, `py -3` can replace `python`; a short project path is recommended.
The first setup requires internet access and space for Lean and Mathlib.
The first command downloads public dependency caches. The Python helper
recompiles all **365 local Lean modules** in dependency order and exits
with a nonzero status if a module fails.

To resume an interrupted build:

```text
python build.py --jobs 3 --resume
```

A standard `lake build` target is also configured.

The audit prints the main theorem signatures and their transitive axiom
dependencies. The expected axioms are only `propext`, `Classical.choice`,
and `Quot.sound`. The final family theorems have no extra Joseph–Polo,
Demazure-character, or PBW hypotheses: this development supplies their proofs.

Recorded checks:

- [provenance/BUILD_CHECK.json](provenance/BUILD_CHECK.json)
- [provenance/ENDPOINT_AUDIT.txt](provenance/ENDPOINT_AUDIT.txt)

To check the distributed snapshot's hashes and local import completeness:

```text
python verify_bundle.py
```

`SHA256SUMS.json` describes this release snapshot. Intentional edits require
updating the hash inventory before that integrity check can pass again.

## Source layout

- `Schubert/RS/Family/`: family data, coefficient evaluation, and final theorems.
- `Schubert/RS/`: keys, atoms, duality, and coefficient extraction.
- `Schubert/RS/JosephPolo/`: presentation and character-formula proofs.
- `Schubert/RS/PBW/`: the ordered-root PBW basis proof.
- `Schubert/RS/Representation/`: representation-theoretic constructions.
- `Schubert/TypeA/`: permutation and divided-difference prerequisites.
- `provenance/`: source inventory and verification records.

## Attribution and licensing

[GrinbergCauchyBinet.lean](Schubert/RS/JosephPolo/GrinbergCauchyBinet.lean)
contains adapted third-party material under **CC BY-NC 4.0**. Its copyright
notice, source attribution, and adjacent
[Grinberg.LICENSE](Schubert/RS/JosephPolo/Grinberg.LICENSE) are retained.
See [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).

Downloaded dependencies retain their own licenses. This repository does not
assign a new blanket license to the other proof files.
