# Lean verification of the key-product counterexamples

This repository (release 2.0.0) contains a Lean 4 formalization of
the main results of Reuven Hodges, *Counterexamples to the Reiner–Shimozono
conjecture and the failure of Schubert filtrations* (2026),
[arXiv:2609.28169](https://arxiv.org/abs/2609.28169).

It proves the coefficient formula for the full counterexample family, its
exact negativity criterion, and an explicit negative coefficient in 28
variables (Theorem 1.1); the failure of relative Schubert filtrations and of
Schubert filtrations in Polo's sense (Corollary 1.2); the failure of
Lascoux-atom positivity (Corollary 1.3); the polytope, counting, positivity
and complexity results for quiver triples (Theorem 1.4); the density of
positive quiver triples (Corollary 1.5); and the quiver multiplicity formula
(Theorem 5.3).

These results are proved with no hypotheses beyond Lean's standard axioms.
The three standard results that the paper cites for Theorems 1.4 and 5.3 are
proved here as well, each by a library of its own: the multiplicities of
polynomial representations of general linear groups and their Levi subgroups
([GLRep](#the-glrep-library)), the polynomial-time decision of rational
feasibility of linear inequalities
([LinearProgramming](#the-linearprogramming-library)), and the saturation of
semi-invariants of quivers, which gives the saturation of quiver
multiplicities ([QuiverInvariants](#the-quiverinvariants-library)); see
[Standard results proved here](#standard-results-proved-here). It uses Lean
**4.35.0-rc3**, a
pinned version of **Mathlib**, and the **Tau Ceti** library. Lean 4.35.0-rc3 is a release candidate; the pin may move to the stable Lean 4.35.0 release.

## AI assistance and verification

**I used GPT-6 Astra and Claude Opus 5.5 to help construct the Lean files.** I
reviewed the definitions, hypotheses, and theorem statements to check that
they faithfully express the intended mathematics and correspond to the
results of the paper listed below.

The development was compiled with Lean, and the final theorems' axiom
dependencies were audited: they use only `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorry`-based proofs or additional unproved axioms.
The mathematical review addresses the correspondence between the formal
statements and the paper, which Lean's proof checking alone does not establish.

## Main results

The entry point is [Schubert/RS/Main.lean](Schubert/RS/Main.lean), which
imports every result below; [docs/STATEMENTS.md](docs/STATEMENTS.md) lists each
labelled statement of the paper with its Lean counterparts.

```lean
import Schubert.RS.Main

open Schubert.RS

#check Family.atomCoefficient_eq_paper
#check Family.not_hasRelativeSchubertFiltration
#check Family.not_lascouxAtomPositive
#check Quiver.Flat.quiverTheorem_identity
#check Quiver.Flat.quiverCoefficient_pos_iff_realPoint
#check Algorithms.quiverPositivity_decision_polyTime
#check Quiver.atomCoefficient_eq_finrank_quiverHom
```

### Theorem 1.1: the counterexample family

For positive integers $p,q$ and an integer scale $\delta\ge p+q$, the paper
defines compositions $a,b,c$ in $4(p+q-1)$ variables and proves

$$
[\mathcal A_c](\kappa_a\kappa_b)
=\frac{p+q-1}{pq}\binom{p+q-2}{p-1}^{2}
 \bigl(2-(p-2)(q-2)\bigr)
=N(p+q-1,p)\bigl(2-(p-2)(q-2)\bigr),
$$

where $N(r,k)=\frac1r\binom rk\binom r{k-1}$ is the Narayana number.
The coefficient is negative exactly when $(p-2)(q-2)>2$. The instances
$(p,q)=(3,5)$ and $(4,4)$ give $-105$ and $-350$ in 28 variables for every
$\delta\ge8$, and the first negative cases within the family occur in 28
variables.

These declarations are in `Schubert.RS.Family`
([Family/Main.lean](Schubert/RS/Family/Main.lean),
[Family/Extras.lean](Schubert/RS/Family/Extras.lean)).

| Declaration | Result |
| --- | --- |
| `atomCoefficient_eq` | The family coefficient as an integer binomial expression |
| `atomCoefficient_eq_paper` | Both displayed expressions, in the rationals |
| `atomCoefficient_eq_narayana` | The Narayana form, in the integers |
| `atomCoefficient_neg_iff` | The exact range of negative coefficients |
| `existsUnique_atomExpansion` | Existence and uniqueness of the integral atom expansion, including the specified coefficient |
| `not_atomPositive` | Failure of atom positivity in the negative range |
| `atomCoefficient_threeFive`, `atomCoefficient_fourFour` | The coefficients −105 and −350 in 28 variables |
| `isLeast_rank_of_negative` | The first negative cases within the family occur in 28 variables |
| `reiner_shimozono_false` | The universal Reiner–Shimozono positivity assertion is false |

| Paper notation | Lean notation |
| --- | --- |
| $\delta$ | `P.K` |
| $p+q-1$ | `P.m` |
| $4(p+q-1)$ variables | `P.rank` |
| $\kappa_a$ | `key a` |
| $\mathcal A_c$ | `atom c` |
| $[\mathcal A_c]f$ | `atomCoefficient f c` |

### Corollary 1.2: Schubert filtrations

For $(p-2)(q-2)>2$, the tensor product $P(-a)\otimes P(-b)$ of dual Joseph
modules admits neither a relative Schubert filtration nor a Schubert
filtration in Polo's sense, already in type $A_{27}$; each factor has an
excellent filtration. The formalization works at the level of modules for the
upper-triangular Borel subalgebra: section modules over unions of Schubert
varieties are twisted duals of sums of Demazure modules in the flag-minor
model, and $P(\nu)$ and $Q(\nu)$ are built from them as in the paper, with
$\mathrm{ch}\,P(-a)=\kappa_a$ and $\mathrm{ch}\,Q(-a)=\mathcal A_a$. The
ambient flag-minor span is proved to be the irreducible module $V(\lambda)$.

| Paper | Lean |
| --- | --- |
| $M$ admits a relative Schubert filtration | `Filtrations.HasRelativeSchubertFiltration M` |
| $M$ admits a Schubert filtration in Polo's sense (layers from unions) | `Filtrations.HasSchubertFiltration M` |
| $P(\nu)$, $Q(\nu)$ | `Filtrations.dualJoseph ν`, `Filtrations.minRelSchubert ν` |
| $P(-a)\otimes P(-b)$ | `Family.familyTensor P` |

The statements are `Family.not_hasRelativeSchubertFiltration`,
`Family.not_hasSchubertFiltration`, their $\mathrm{SL}_n$ forms
`Family.not_hasSLRelativeSchubertFiltration` and
`Family.not_hasSLSchubertFiltration`, and `Family.typeA27_filtration_failure`
([Family/FiltrationCorollary.lean](Schubert/RS/Family/FiltrationCorollary.lean)).

### Corollary 1.3: Lascoux polynomials

For $(p-2)(q-2)>2$, the product of the Lascoux polynomials of $a$ and $b$ has
no expansion in Lascoux atoms with coefficients in
$\mathbb Z_{\ge0}[\beta]$ (`Family.not_lascouxAtomPositive`), nor even one
with coefficients in $\mathbb Z[\beta]$ that are nonnegative at $\beta=0$
(`Family.no_lascouxExpansion_nonnegAtZero`). Lascoux polynomials are
defined, as in Lascoux's original definition, by the K-theoretic isobaric
divided difference operators
$\pi_i^{(\beta)}f=\pi_i\bigl((1+\beta x_{i+1})f\bigr)$, and Lascoux atoms by the
operators $\pi_i^{(\beta)}-1$ ([Lascoux/](Schubert/RS/Lascoux)).

### Corollary 1.5: positive quiver triples have positive density

For $n\ge4$, the number of quiver triples $a,b,c\in\lbrace0,\ldots,H\rbrace^n$
with $[\mathcal A_c](\kappa_a\kappa_b)>0$ is $\Theta(H^{3n-1})$, a proportion
bounded away from zero among the triples with $|a|+|b|=|c|$
(`Quiver.Density.card_positiveQuiverTriples_isTheta`,
`Quiver.Density.positiveQuiverTriples_proportion`). The proof goes through the
two-source case of the quiver multiplicities, where the atom coefficient is a
Kostka number (`Quiver.twoSource_eq_kostka`, `Quiver.twoSource_pos_iff`).

### Theorem 1.4: quiver triples

A triple of lists $a,b,c$ of natural numbers is read as weak compositions of
length $n=|c|$. For a quiver triple, with its canonical interval partition
$\mathcal I$, the quiver $Q$ and the weights $\lambda^{(p)}$ of the paper, the
polytope $P(a,b,c)\subseteq\mathbb R^M$ is the explicit system of linear
inequalities `Quiver.Flat.quiverPolytope a b c`, with $M=2n^3+2n^4$ variables
and coefficients in $\lbrace -1,0,1\rbrace$. The counting identity

$$
[\mathcal A_c](\kappa_a\kappa_b)
=\dim\mathrm{Hom}_{L_{\mathcal I}}\Bigl(\bigotimes_{p}V_p^{\lambda^{(p)}},\mathcal R_Q\Bigr)
=\bigl\lvert P(a,b,c)\cap\mathbb Z^M\bigr\rvert
$$

holds for every quiver triple (`Quiver.Flat.quiverTheorem_identity`). The
coefficient is positive exactly when $P(a,b,c)$ is nonempty, and positivity
is decidable in polynomial time. The positivity criterion uses the
saturation of quiver multiplicities, proved by the
[QuiverInvariants](#the-quiverinvariants-library) library. Without it,
$P(a,b,c)$ is nonempty exactly when some dilation $(Na,Nb,Nc)$ with $N\ge1$
has a positive coefficient, and the dilated coefficients count the integer
points of the dilated polytopes.

| Declaration | Result |
| --- | --- |
| `Quiver.Flat.quiverTheorem_identity` | The counting identity, with a finite-dimensional Hom space |
| `Quiver.Flat.quiverPolytope_card` | The outer equality, and finiteness of the integer points |
| `Quiver.Flat.quiverPolytope_bounded` | $P(a,b,c)$ is bounded |
| `Quiver.Flat.quiverCoefficient_pos_iff_realPoint` | The coefficient is positive iff $P(a,b,c)$ has a real point |
| `Quiver.Flat.quiverCoefficient_pos_iff_ratPoint` | The coefficient is positive iff $P(a,b,c)$ has a rational point |
| `Quiver.Flat.quiverPolytope_nonempty_iff_exists_nsmul_pos` | $P(a,b,c)$ is nonempty iff some dilation has a positive coefficient |
| `Quiver.Flat.atomCoefficient_nsmul_eq_card` | The dilated coefficients count the integer points of the dilated polytopes |
| `Algorithms.quiverTriple_recognition` | Recognizing quiver triples in polynomial time |
| `Algorithms.quiverPolytope_construction` | Constructing $P(a,b,c)$ in polynomial time |
| `Algorithms.quiverPositivity_decision_polyTime` | Deciding positivity in polynomial time |

The intermediate theorems `Quiver.Flat.quiverTheorem_counts`,
`Quiver.Flat.quiverCoefficient_pos_iff_nonempty`,
`Quiver.Flat.quiverCoefficient_pos_iff_ratFeasible` and
`Algorithms.quiverPositivity_decision` take the standard results they use as
explicit hypotheses; the corresponding rows of the table apply the proofs of
`GLCharacterMultiplicity`, `QuiverSaturation` and
`PolyTimeRationalFeasibility` to them
([Main/Unconditional.lean](Schubert/RS/Main/Unconditional.lean)).

Polynomial time is `Complexity.FP` from complexitylib (deterministic
multi-tape Turing machines), with the input encoded in binary
(`Algorithms.encodeTriple`, whose length is linear in the binary size of
$(a,b,c)$).

### Theorem 5.3: the quiver multiplicity

For a quiver partition $\mathcal I$ of $(a,b,c)$,
`Quiver.atomCoefficient_eq_finrank_quiverHom` gives

$$
[\mathcal A_c](\kappa_a\kappa_b)
=\dim\mathrm{Hom}_{L_{\mathcal I}}\Bigl(\bigotimes_p V_p^{\lambda^{(p)}},\mathcal R_Q\Bigr),
$$

where $L_{\mathcal I}=\prod_p\mathrm{GL}(V_p)$ acts on the coordinate ring
$\mathcal R_Q$ of the representation space of the quiver $Q$, and the
$V_p^{\lambda^{(p)}}$ are irreducible rational representations
(`GL.ratLeviIrrep`, built from flag minors). At the level of characters, the
coefficient is the multiplicity of $\prod_p s_{\lambda^{(p)}}$ in the graded
character of $\mathcal R_Q$ (`Quiver.atomCoefficient_eq_multiplicity`), and
it is nonnegative (`Quiver.atomCoefficient_nonneg`). The passage from
characters to Hom spaces is the multiplicity theorem of the GLRep library,
through the proof `glCharacterMultiplicity_holds` of
`GLCharacterMultiplicity`; the endpoint with that statement as a hypothesis is
`Quiver.atomCoefficient_eq_finrank_hom`.

### The GLRep library

[Schubert/GLRep/](Schubert/GLRep) (namespace `GLRep`) develops the polynomial
and rational representations of $\mathrm{GL}_n(K)$ and of Levi groups
$\prod_p\mathrm{GL}_{d_p}(K)$ over a field $K$ of characteristic zero,
through the representations of the Lie algebra $\mathfrak{gl}_n(K)$; no
algebraic closure is needed. It proves the Weyl character formula for
$\mathfrak{gl}_n$, complete reducibility, the classification of the
irreducible polynomial representations $V(\mu)$ by Young diagrams $\mu$ with
at most $n$ rows, with the Schur polynomials $s_\mu$ as characters, and the
expansion of every character in Schur polynomials with the multiplicities
$\dim\mathrm{Hom}(V(\mu),\rho)$. Twists by powers of the determinant
extend these results to rational representations. Together with these
twists, the multiplicity theorem for Levi groups proves
`GLCharacterMultiplicity` (`glCharacterMultiplicity_holds`,
[GL/CharacterMultiplicity.lean](Schubert/RS/GL/CharacterMultiplicity.lean)).

| Declaration | Result |
| --- | --- |
| `GLRep.alternant_mul_glCharacter_of_isGlHighestWeightVector` | The Weyl character formula for $\mathfrak{gl}_n$ |
| `GLRep.IsPolynomialRep.isSemisimpleRepresentation` | Complete reducibility of polynomial representations |
| `GLRep.isIrreducible_irrep`, `GLRep.character_irrep` | $V(\mu)$ is irreducible, with character $s_\mu$ |
| `GLRep.IsPolynomialRep.exists_nonempty_equiv_irrep` | Every irreducible polynomial representation is some $V(\mu)$ |
| `GLRep.IsPolynomialRep.nonempty_equiv_of_character_eq` | Irreducible polynomial representations with equal characters are equivalent |
| `GLRep.finrank_intertwiningMap_irrep_self`, `GLRep.finrank_intertwiningMap_irrep_of_ne` | Schur's lemma for the $V(\mu)$ |
| `GLRep.IsPolynomialRep.exists_character_eq_sum` | $\mathrm{ch}\,\rho=\sum_\mu\dim\mathrm{Hom}(V(\mu),\rho)\,s_\mu$ |
| `GLRep.IsPolynomialLeviRep.exists_leviCharacter_eq_sum` | The same expansion for Levi groups, in products of Schur polynomials |
| `GLRep.IsRationalRep.isSemisimpleRepresentation` | Complete reducibility of rational representations |
| `GLRep.IsRationalRep.exists_nonempty_equiv_ratIrrep` | Every irreducible rational representation is some $V(\lambda)$, $\lambda\in\mathbb Z^n$ dominant |
| `GLRep.IsRationalRep.exists_ratCharacter_eq_sum`, `GLRep.IsRationalLeviRep.exists_ratLeviCharacter_eq_sum` | The character expansions of rational representations, in rational Schur polynomials |

### The LinearProgramming library

[Schubert/LinearProgramming/](Schubert/LinearProgramming) (namespace
`LinearProgramming`) decides in polynomial time whether a finite system
$Ax\le b$ of linear inequalities with integer coefficients has a rational
solution (`LinearProgramming.exists_mem_FP_feasible`, on the binary encoding
`LinearProgramming.encodeSystem`). The algorithm is of Chubanov type: after a
perturbation, the system becomes a homogeneous system $My=0$, $y>0$, which is
solved by alternating projections and rescalings, with exact integer
arithmetic throughout (Bareiss elimination for the projections). Polynomial
time is `Complexity.FP` from complexitylib, as above. This proves
`PolyTimeRationalFeasibility` (`polyTimeRationalFeasibility_holds`,
[Complexity/RationalFeasibility.lean](Schubert/RS/Complexity/RationalFeasibility.lean)).

| Declaration | Result |
| --- | --- |
| `LinearProgramming.exists_mem_FP_feasible` | Rational feasibility of integer systems is decidable in polynomial time |
| `LinearProgramming.decideFeasible_iff` | The decision procedure accepts exactly the feasible systems |
| `LinearProgramming.chubanov_iff` | Correctness of the projection-and-rescaling algorithm |

### The QuiverInvariants library

[Schubert/QuiverInvariants/](Schubert/QuiverInvariants) (namespace
`QuiverInvariants`) proves, over any infinite field, the theorem of Derksen
and Weyman that the weights of semi-invariants of a quiver without oriented
cycles are saturated, following Baldoni, Vergne and Walter. The steps are
Schofield's formula for the general dimension of $\mathrm{Ext}$, King's
inequalities, determinantal semi-invariants, and the resulting
characterization of the weights of nonzero semi-invariants (Theorem 4.2 of
Baldoni–Vergne–Walter). Schofield's bound is proved by an elementary route:
for a general pair of representations, homomorphisms are unobstructed, and
dividing by the image of a homomorphism does not change $\mathrm{Ext}$; the
proof uses only polynomial identities, ranks, minors and Zariski density,
rather than the geometric argument. The library depends only on Mathlib and
on `Schubert/GLRep/Polynomial/Functions.lean`. Together with the identity
that expresses a quiver multiplicity as the multiplicity of a constant weight
on a flag quiver, and the description of positive multiplicities of constant
weights by semi-invariants, this proves `QuiverSaturation`
(`quiverSaturation_holds`,
[Quiver/Saturation.lean](Schubert/RS/Quiver/Saturation.lean)).

| Declaration | Result |
| --- | --- |
| `QuiverInvariants.FQuiver.exists_generalQuot_euler_add_extDim_nonpos` | Schofield's bound |
| `QuiverInvariants.FQuiver.isGreatest_genericExt` | Schofield's formula $\mathrm{ext}(\alpha,\beta)=\max\lbrace-\langle\alpha,\beta''\rangle : \beta\twoheadrightarrow\beta''\rbrace$ |
| `QuiverInvariants.FQuiver.IsSemiInvariant.sum_mul_nonneg_of_generalQuot` | King's inequalities |
| `QuiverInvariants.FQuiver.exists_semiInvariant_iff` | The weights of nonzero semi-invariants (Baldoni–Vergne–Walter, Theorem 4.2) |
| `QuiverInvariants.FQuiver.exists_semiInvariant_of_nsmul` | Saturation of the weights of semi-invariants (Derksen–Weyman) |
| `Quiver.ForwardQuiver.multiplicity_flag` | A quiver multiplicity is a multiplicity of a constant weight on the flag quiver |
| `Quiver.ForwardQuiver.multiplicity_const_pos_iff` | Multiplicities of constant weights are positive iff there is a nonzero semi-invariant |
| `quiverSaturation_holds` | The saturation of quiver multiplicities |

## Standard results proved here

The paper cites three standard results for Theorems 1.4 and 5.3. Each is stated
as a Lean proposition in [Schubert/RS/Statements/](Schubert/RS/Statements) and
proved here by a library of its own. Some intermediate theorems take one of
these results as an explicit hypothesis;
[Main/Unconditional.lean](Schubert/RS/Main/Unconditional.lean) applies the
proofs to them, and the audit prints every signature.

| Result | Source | Proof | Library |
| --- | --- | --- | --- |
| [`QuiverSaturation`](Schubert/RS/Statements/QuiverSaturation.lean) | H. Derksen, J. Weyman, Semi-invariants of quivers and saturation for Littlewood-Richardson coefficients, J. Amer. Math. Soc. 13 (2000); in the form for multiplicities in the coordinate ring: V. Baldoni, M. Vergne, M. Walter, arXiv:1901.07194, Section 8. | `quiverSaturation_holds` | [`Schubert/QuiverInvariants/`](Schubert/QuiverInvariants) |
| [`PolyTimeRationalFeasibility`](Schubert/RS/Statements/PolyTimeRationalFeasibility.lean) | L. G. Khachiyan, A polynomial algorithm in linear programming, Dokl. Akad. Nauk SSSR 244 (1979); E. Tardos, A strongly polynomial algorithm to solve combinatorial linear programs, Oper. Res. 34 (1986). | `polyTimeRationalFeasibility_holds` | [`Schubert/LinearProgramming/`](Schubert/LinearProgramming) |
| [`GLCharacterMultiplicity`](Schubert/RS/Statements/GLCharacterMultiplicity.lean) | Complete reducibility, characters of irreducible polynomial representations, and Schur's lemma: W. Fulton, J. Harris, Representation Theory, Lectures 6 and 15; R. Stanley, Enumerative Combinatorics 2, Appendix 2, Theorem A2.4. | `glCharacterMultiplicity_holds` | [`Schubert/GLRep/`](Schubert/GLRep) |

## Build and verify

Install [Lean and Lake through elan](https://lean-lang.org/install/) and
[Python 3](https://www.python.org/downloads/). Git must also be available.
The `lean-toolchain` file selects Lean 4.35.0-rc3 automatically, and
`lake-manifest.json` pins Mathlib, Tau Ceti and their public dependencies.

From the repository directory, run:

```text
lake exe cache get
python build.py --jobs 3
lake env lean Schubert/RS/Audit.lean
```

On Windows, `py -3` can replace `python`; a short project path is recommended.
The first setup requires internet access and space for Lean and Mathlib.
The first command downloads public dependency caches. The Python helper first
has Lake build the Tau Ceti modules used here and the vendored complexitylib
files, then recompiles all **565 local Lean modules** in dependency
order, and exits with a nonzero status if a module fails.

To resume an interrupted build, or to check that every module was compiled
from the current sources:

```text
python build.py --jobs 3 --resume
python build.py --check
```

A standard `lake build` target is also configured.

The audit prints the main theorem signatures, with their hypotheses, and their
transitive axiom dependencies. The expected axioms are only `propext`,
`Classical.choice`, and `Quot.sound`.

Recorded checks:

- [provenance/BUILD_CHECK.json](provenance/BUILD_CHECK.json)
- [provenance/ENDPOINT_AUDIT.txt](provenance/ENDPOINT_AUDIT.txt)

To check the distributed snapshot's hashes, the local import completeness and
the vendored files against their upstream hashes:

```text
python verify_bundle.py
```

`SHA256SUMS.json` describes this release snapshot. Intentional edits require
updating the hash inventory before that integrity check can pass again.

## Source layout

- `Schubert/RS/Family/`: family data, coefficient evaluation, and the final
  theorems of Theorem 1.1 and Corollaries 1.2 and 1.3.
- `Schubert/RS/`: keys, atoms, duality, and coefficient extraction.
- `Schubert/RS/Window/`: the rational extraction formula.
- `Schubert/RS/Hall/`: the Hall polynomial extraction of Section 3 for general
  Hall triples (Lemmas 3.1 and 3.8, Definition 3.9, Proposition 3.11).
- `Schubert/RS/BModules/`, `Schubert/RS/SchubertUnions/`,
  `Schubert/RS/Filtrations/`: modules for the Borel subalgebra, sums of
  Demazure modules, and filtrations.
- `Schubert/RS/HighestWeight/`: the flag-minor span as the irreducible module
  $V(\lambda)$.
- `Schubert/RS/Lascoux/`: Lascoux polynomials and atoms.
- `Schubert/RS/Quiver/`, `Schubert/RS/GL/`: quiver triples, their
  multiplicities, the representations of Theorem 5.3, and the polytope
  $P(a,b,c)$ (`Quiver/Polytope/`).
- `Schubert/RS/LR/`: the Littlewood–Richardson rule used for the counting
  identity.
- `Schubert/RS/Polyhedra/`: systems of integer linear inequalities, their
  real, rational and integer points.
- `Schubert/RS/Complexity/`: encodings and polynomial-time algorithms.
- `Schubert/RS/Statements/`: the standard results cited by the paper, stated
  as Lean propositions (each proved here).
- `Schubert/RS/Main/`: the endpoints of each part; `Main/Unconditional.lean`
  applies the proofs of the standard results to the theorems that take them
  as hypotheses.
- `Schubert/GLRep/`: polynomial and rational representations of general
  linear groups and their Levi groups in characteristic zero.
- `Schubert/LinearProgramming/`: polynomial-time rational feasibility of
  systems of linear inequalities.
- `Schubert/QuiverInvariants/`: semi-invariants of quivers, Schofield's
  formula and the Derksen–Weyman saturation theorem.
- `Schubert/RS/JosephPolo/`, `Schubert/RS/PBW/`,
  `Schubert/RS/Representation/`: presentation, character-formula and PBW
  proofs.
- `Schubert/TypeA/`: permutation and divided-difference prerequisites.
- `vendor/complexitylib/`: 197 vendored source files of complexitylib.
- `docs/STATEMENTS.md`: the statements of the paper and their Lean
  counterparts.
- `provenance/`: source inventory and verification records.

## Attribution and licensing

This repository is licensed under the [Apache License 2.0](LICENSE), except
for the third-party file described below. Redistributions must retain the
[NOTICE](NOTICE) file. If you use or adapt this code, please cite the paper
([arXiv:2609.28169](https://arxiv.org/abs/2609.28169)) and this repository;
citation metadata is in [CITATION.cff](CITATION.cff).

[GrinbergCauchyBinet.lean](Schubert/RS/JosephPolo/GrinbergCauchyBinet.lean)
contains adapted third-party material under **CC BY-NC 4.0** and is not
covered by the Apache License. Its copyright notice, source attribution, and
adjacent [Grinberg.LICENSE](Schubert/RS/JosephPolo/Grinberg.LICENSE) are
retained. The files in [vendor/complexitylib](vendor/complexitylib) are
unmodified sources of complexitylib under the Apache License 2.0, with its
license in [vendor/complexitylib/LICENSE](vendor/complexitylib/LICENSE). See
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).

Downloaded dependencies retain their own licenses.
