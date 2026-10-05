# Lean verification of *Counterexamples to the Reiner–Shimozono conjecture and the failure of Schubert filtrations*

This repository (release 2.1.0) contains a Lean 4 formalization of
the main results of Reuven Hodges, *Counterexamples to the Reiner–Shimozono
conjecture and the failure of Schubert filtrations* (2026),
[arXiv:2609.28169](https://arxiv.org/abs/2609.28169).

It proves the coefficient formula for the full counterexample family, its
exact negativity criterion, and an explicit negative coefficient in 28
variables (Theorem 1.1); the failure of relative Schubert filtrations and of
Schubert filtrations in Polo's sense for modules of global sections of line
bundles on Schubert varieties (Corollary 1.2); the failure of
Lascoux-atom positivity (Corollary 1.3); the polytope, counting, positivity
and complexity results for quiver triples (Theorem 1.4); the density of
positive quiver triples (Corollary 1.5); and the quiver multiplicity formula
(Theorem 5.3).

These results are proved with no hypotheses beyond Lean's standard axioms.
The standard results that the paper relies on are proved here as well, each by
a library of its own: the multiplicities of polynomial representations of
general linear groups and their Levi subgroups ([GLRep](#the-glrep-library)),
the polynomial-time decision of rational feasibility of linear inequalities
([LinearProgramming](#the-linearprogramming-library)), and the saturation of
semi-invariants of quivers, which gives the saturation of quiver
multiplicities ([QuiverInvariants](#the-quiverinvariants-library)), all three
cited for Theorems 1.4 and 5.3; and the theory of flag varieties, Schubert
varieties, line bundles and Demazure modules behind Corollary 1.2
([flag varieties](#the-flag-variety-library)); see
[Standard results proved here](#standard-results-proved-here). It uses Lean
**4.35.0-rc3**, a
pinned version of **Mathlib**, and the **Tau Ceti** library. Lean 4.35.0-rc3 is a release candidate; the pin may move to the stable Lean 4.35.0 release.

The flag-variety library is self-contained and may be of interest beyond this
paper: it imports only Mathlib and Tau Ceti, and it is versioned separately
from this repository.

## AI assistance and verification

**I used GPT-6 Astra and Claude Opus 5.5 to help construct the Lean files.** I
reviewed all definitions, hypotheses, and theorem statements to check that
they faithfully express the intended mathematics, including the results of
the paper listed below.

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
#check Geometric.not_hasGeometricRelativeSchubertFiltration
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
filtration in Polo's sense, over $\mathrm{GL}_n$ or over $\mathrm{SL}_n$,
already in type $A_{27}$; each factor has an excellent filtration.

This is formalized for the modules of the paper, which are spaces of global
sections of line bundles on Schubert varieties over $\mathbb C$. The flag
variety is the flag scheme $\mathrm{Fl}_n=\mathrm{GL}_n/B$ of the
[flag-variety library](#the-flag-variety-library), with $B$ the Borel subgroup
of upper triangular matrices. The Schubert variety $X_w$ is the
scheme-theoretic image of the orbit map $b\mapsto b\dot w$; unions $X_S$ of
Schubert varieties and Schubert boundaries $\partial X_\sigma$ are closed
subschemes of $\mathrm{Fl}_n$ as well. The line bundle
$\mathcal L(\eta)=\mathrm{GL}_n\times^B\mathbb C_\eta$ is pulled back to each
of them, and $B$ acts on the global sections by left translation. With
$\sigma=\sigma(\nu)$ and $\eta=\eta(\nu)$ as in the paper,

$$
P(\nu)=H^0\bigl(X_\sigma,\mathcal L(\eta)\bigr),\qquad
Q(\nu)=\ker\Bigl(H^0\bigl(X_\sigma,\mathcal L(\eta)\bigr)\to H^0\bigl(\partial X_\sigma,\mathcal L(\eta)\bigr)\Bigr),
$$

with $\mathrm{ch}\,P(-u)=\kappa_u$ and $\mathrm{ch}\,Q(-u)=\mathcal A_u$. The
layers of a Schubert filtration in Polo's sense are the modules
$H^0(X_S,\mathcal L(\eta))$ for nonempty Bruhat order ideals $S$ and
antidominant weights $\eta$.

| Paper | Lean |
| --- | --- |
| $X_w$, $X_S$, $\partial X_\sigma\subseteq\mathrm{Fl}_n$ | `FlagVarieties.schubertVariety`, `FlagVarieties.schubertUnion`, `FlagVarieties.schubertBoundary` |
| $\mathcal L(\eta)$, $H^0(X,\mathcal L(\eta))$ | `FlagVarieties.lineBundle`, `FlagVarieties.sections` |
| The action of $B$ on $H^0(X,\mathcal L(\eta))$ | `FlagVarieties.sectionsRep` |
| Restriction of sections from $X$ to $X'\subseteq X$ | `FlagVarieties.sectionsRestrict` |
| $P(\nu)$, $Q(\nu)$ | `FlagVarieties.dualJoseph ν`, `Geometric.geometricMinimalRelativeSchubert ν` |
| $P(-a)\otimes P(-b)$ | `Geometric.geometricFamilyTensor P` |
| $M$ admits a relative Schubert filtration | `Geometric.HasGeometricRelativeSchubertFiltration M` |
| $M$ admits a Schubert filtration in Polo's sense (layers from unions) | `Geometric.HasGeometricSchubertFiltration M` |
| The same over $\mathrm{SL}_n$ | `Geometric.HasGeometricSLRelativeSchubertFiltration M`, `Geometric.HasGeometricSLSchubertFiltration M` |

The statements are `Geometric.not_hasGeometricRelativeSchubertFiltration`,
`Geometric.not_hasGeometricSchubertFiltration`, their $\mathrm{SL}_n$ forms
`Geometric.not_hasGeometricSLRelativeSchubertFiltration` and
`Geometric.not_hasGeometricSLSchubertFiltration`, and
`Geometric.typeA27_geometricFiltration_failure`
([Geometric/SchemeRelative.lean](Schubert/RS/Geometric/SchemeRelative.lean),
[Geometric/SchemeCorollary.lean](Schubert/RS/Geometric/SchemeCorollary.lean)).
Their only hypothesis is $(p-2)(q-2)>2$, and $\delta\ge8$ in type $A_{27}$.
The characters are `FlagVarieties.ch_dualJoseph_negWeight`,
`Geometric.ch_geometricMinimalRelativeSchubert_negWeight` and
`Geometric.ch_geometricFamilyTensor`. As in the paper, a filtration of either
kind would make $\kappa_a\kappa_b$ a nonnegative integral combination of
atoms, contradicting Theorem 1.1.

#### The algebraic model

The characters are computed in an algebraic model, which was the form of
Corollary 1.2 in release 2.0.0 and is kept in this release. Global sections
are semi-invariants: $H^0(X,\mathcal L(\eta))$ is the module of functions on
the preimage of $X$ in $\mathrm{GL}_n$ that transform by the weight $\eta$
under right translation by $B$ (`FlagVarieties.sectionsEquivSemiInvariants`,
over every commutative ring). For $X=X_S$ this is the ring model of the
section module (`FlagVarieties.geometricSectionEquiv`), and $P(\nu)$ and
$Q(\nu)$ agree with their ring-model versions
(`FlagVarieties.dualJosephEquiv`,
`Geometric.geometricMinimalRelativeSchubertEquiv`). For $\eta=-\lambda$, with
$\lambda$ a partition, the section module is the twisted dual of the sum of
Demazure modules described next, as a module for the Borel subalgebra
(`FlagVarieties.sectionBModuleIso`, in the copy of this construction that
belongs to the flag-variety library).

In the algebraic model, the formalization works at the level of modules for
the upper-triangular Borel subalgebra: section modules over unions of
Schubert varieties are twisted duals of sums of Demazure modules in the
flag-minor model, and $P(\nu)$ and $Q(\nu)$ are built from them as in the
paper, with $\mathrm{ch}\,P(-a)=\kappa_a$ and $\mathrm{ch}\,Q(-a)=\mathcal A_a$.
The ambient flag-minor span is proved to be the irreducible module
$V(\lambda)$.

| Paper | Lean |
| --- | --- |
| $M$ admits a relative Schubert filtration | `Filtrations.HasRelativeSchubertFiltration M` |
| $M$ admits a Schubert filtration in Polo's sense (layers from unions) | `Filtrations.HasSchubertFiltration M` |
| $P(\nu)$, $Q(\nu)$ | `Filtrations.dualJoseph ν`, `Filtrations.minRelSchubert ν` |
| $P(-a)\otimes P(-b)$ | `Family.familyTensor P` |

The module-level statements are `Family.not_hasRelativeSchubertFiltration`,
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
The [flag-variety library](#the-flag-variety-library) builds on it and adds
the rational representations of the Borel subgroup (`Schubert/GLRep/Borel/`,
`Schubert/GLRep/BorelLie/`).

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

### The flag-variety library

The folders [Schubert/FlagVarieties/](Schubert/FlagVarieties),
[Schubert/Demazure/](Schubert/Demazure) and [Schubert/TypeA/](Schubert/TypeA),
together with the [GLRep library](#the-glrep-library) and its extension to the
Borel subgroup (`Schubert/GLRep/Borel/`, `Schubert/GLRep/BorelLie/`), develop
flag varieties, Schubert varieties, and the representations of the Borel
subgroup on the sections of line bundles over them. Corollary 1.2 is stated
and proved for the objects defined here
([Schubert/RS/Geometric/](Schubert/RS/Geometric)). The library imports only
Mathlib and Tau Ceti, and nothing from `Schubert/RS/`, so it can be reused by
other projects. It is versioned separately: release 2.1.0 contains
its version 0.1.0, and [FLAG_MODULE_MANIFEST.json](FLAG_MODULE_MANIFEST.json)
records its folders and the SHA-256 hash of each of its 785 files, so that a
copy elsewhere can be compared with this one file by file.

The schemes are defined over an arbitrary commutative ring $R$. Results about
points, dimension, normality and Fulton's conditions are over a field, with
the hypotheses (infinite, characteristic zero, algebraically closed) stated in
each declaration; the Demazure library and the comparison with
representations of $\mathrm{GL}_n(\mathbb C)$ are over $\mathbb C$. The main
namespaces are `FlagVarieties` (with `FlagVarieties.PointModel`, the model by
functions on $\mathrm{GL}_n(K)$ over a field $K$), `Demazure`, `GLRep` and
`Schubert.FinPermutation`. In the table, names without one of the prefixes
`Demazure.`, `GLRep.` or `Schubert.` are in the namespace `FlagVarieties`.

| Topic | Declarations | Content |
| --- | --- | --- |
| The flag scheme and $\mathrm{GL}_n/B$ | `FlagScheme`, `FlagScheme.isProper_toSpec`, `isColimitOrbitMap`, `exists_mulRight_eq` | The complete flag scheme $\mathrm{Fl}_n$ over $\mathrm{Spec}\,R$ is proper. The orbit map $\pi:\mathrm{GL}_n\to\mathrm{Fl}_n$ is the coequalizer of the projection and the right action $\mathrm{GL}_n\times_R B\rightrightarrows\mathrm{GL}_n$ in the category of schemes, and its fibres over affine schemes are $B$-orbits |
| Schubert varieties | `schubertVariety`, `schubertUnion`, `schubertBoundary`, `isIntegral_schubertVariety`, `schubertVariety_globalSections_const`, `PointModel.schubertVariety_le_iff` | $X_w$ is the scheme-theoretic image of $b\mapsto b\dot w$ from $B$ to $\mathrm{Fl}_n$; unions and boundaries are given by their ideal sheaves. Over a field $K$, $X_w$ is integral with $\Gamma(X_w,\mathcal O)=K$, and $X_v\subseteq X_w$ iff $v\le w$ (characteristic zero) |
| Opposite Schubert and Richardson varieties | `oppositeSchubertVariety`, `richardsonVariety`, `Richardson.richardsonVariety_ne_top_iff` | $X^w$, the closure of $B^-\dot wB/B$, and $X_w^v=X_w\cap X^v$ as a scheme-theoretic intersection, which is nonempty iff $v\le w$ (characteristic zero) |
| Line bundles and sections | `lineBundle`, `isInvertible_lineBundle`, `sections`, `sectionsEquivSemiInvariants`, `sectionsRestrict`, `sectionsMul` | $\mathcal L(\eta)=\mathrm{GL}_n\times^B R_\eta$ is invertible. For a closed subscheme $X$, $H^0(X,\mathcal L(\eta))$ is the module of semi-invariants of weight $\eta$ in the coordinate ring of $\pi^{-1}(X)$; restriction and multiplication of sections |
| The action of $B$ | `sectionsRep`, `sectionsComodule`, `contract_sectionsComodule` | $B(R)$ acts on $H^0(X,\mathcal L(\eta))$ by left translation when $\pi^{-1}(X)$ is stable under $B$. The same action as a comodule over the coordinate ring $\mathcal O(B)$, which gives back the action on points |
| Rational representations of $B$ | `GLRep.rationalBorelRepEquivComodule`, `GLRep.indBorelFrobeniusEquiv`, `GLRep.IsRationalBorelRep.toBModule` | Weights, characters and filtrations of rational representations of $B(K)$. Over an infinite field, the finite-dimensional ones are the same as $\mathcal O(B)$-comodules; induction from $B$ to $\mathrm{GL}_n$ and Frobenius reciprocity. Over $\mathbb C$, a rational representation is a module for $\mathfrak n^+$ with a compatible torus action, with the same subrepresentations and intertwining maps |
| Projective normality | `PointModel.sectionsRestrict_surjective`, `PointModel.schubertSectionsBasis`, `PointModel.geometricSectionRingEquiv` | For a Bruhat order ideal $S$ and a partition $\lambda$, restriction $H^0(\mathrm{Fl}_n,\mathcal L(-\lambda))\to H^0(X_S,\mathcal L(-\lambda))$ is surjective and $H^0(X_S,\mathcal L(-\lambda))$ has a standard-monomial basis; the section ring $\bigoplus_\lambda H^0(X_S,\mathcal L(-\lambda))$ is the quotient of the flag-minor algebra by the ideal of $X_S$ (algebraically closed fields of characteristic zero) |
| Borel–Weil | `PointModel.minorSpanEquivSections`, `borelWeil_ratIrrep` | For a partition $\lambda$, $H^0(\mathrm{Fl}_n,\mathcal L(-\lambda))$ is spanned by the products of flag minors of shape $\lambda$; for a dominant weight $\lambda$, it is $V(\lambda)^\vee$ as a representation of $\mathrm{GL}_n(\mathbb C)$ |
| Demazure modules | `Demazure.FlagModule.flagDemazure`, `Demazure.FlagModule.compositionFlagJosephPolo`, `Demazure.SchubertUnions.flagDemazure_hasTorusCharacter`, `Demazure.SchubertUnions.key_eq_sum_atom`, `nonempty_sectionDemazureEquiv_ratIrrep`, `sectionBModuleIso` | The Demazure modules $D_w(\lambda)$ in the flag-minor model, their Joseph–Polo presentation, the character formula $\mathrm{ch}\,D_w(\lambda)=\kappa_{w\lambda}$, and $\kappa_{\sigma\lambda}=\sum_{u\le\sigma}\mathcal A_{u\lambda}$. For a Bruhat order ideal $S$, $H^0(X_S,\mathcal L(-\lambda))\cong\bigl(\sum_{w\in S}D_w(\lambda)\bigr)^\vee$ as representations of $B$, and as modules for $\mathfrak n^+$ and the torus |
| Fulton's rank conditions and Kazhdan–Lusztig patches | `PointModel.orbitIdeal_lowerSet_eq_fultonIdeal`, `PointModel.isRadical_map_fultonIdeal`, `PointModel.map_kazhdanLusztigSubst_fultonIdeal`, `PointModel.isRadical_map_kazhdanLusztigSubst_fultonIdeal` | Fulton's rank conditions generate the ideal of $\pi^{-1}(X_w)$ in $\mathcal O(\mathrm{GL}_n)$ and the ideal of the Kazhdan–Lusztig patch of $X_w$ at $v$, and both ideals are radical (algebraically closed fields of characteristic zero) |
| Bruhat cells and dimension | `PointModel.cellRingEquiv`, `Dimension.topologicalKrullDim_schubertVariety`, `Bruhat.permCoxeterSystem`, `Bruhat.bruhatLE_iff_strongBruhatLE` | Over a field, the Bruhat cell of $w$ is an affine space of dimension $\ell(w)$; $\dim X_w=\ell(w)$ (algebraically closed fields of characteristic zero). $S_{n+1}$ is the Coxeter group of type $A_n$, and its Bruhat order is the rank-matrix order |
| The Plücker embedding | `Plucker.plucker`, `Plucker.pluckerSegre`, `Plucker.isClosedImmersion_pluckerSegre`, `PointModel.pluckerVector_proportional_iff` | The Plücker morphisms $\mathrm{Fl}_n\to\mathbb P(\wedge^{k}R^n)$, given by the flag minors, and the Segre–Plücker morphism to $\mathbb P(\bigotimes_k\wedge^kR^n)$, a closed immersion over every commutative ring. Over a field, $gB=g'B$ iff the Plücker vectors of $g$ and $g'$ are proportional |
| The rank-one functor | `rankOneInduction`, `rankOneInductionSectionsEquiv`, `simpleSchubertSectionsEquiv`, `ch_rankOneInduction_charCoaction` | $H_{s_i}(M)=(\mathcal O(P_i)\otimes M)^B$ for the minimal parabolic subgroup $P_i$. For a character, $H_{s_i}(R_\eta)\cong H^0(X_{s_i},\mathcal L(\eta))$, a free module of rank $\max(0,d+1)$, $d=-\langle\eta,\alpha_i^\vee\rangle$, identified with the binary forms of degree $d$; over a field its character is $\pi_i(x^{-\eta})$ for $d\ge-1$ |
| Permutations | `Schubert.FinPermutation.strongBruhatLE_iff_northwestRankNat`, `Schubert.FinPermutation.strongBruhatLE_iff_reduced_adjacent_subword` | The Bruhat order by rank matrices and by subwords of reduced words, essential sets, and divided differences ([Schubert/TypeA/](Schubert/TypeA)) |

Not formalized in version 0.1.0 of the library:

- Twisting sheaves. $\mathcal O(d)$ on $\mathrm{Proj}$, and on
  $\mathbb P^1$, is not defined in the module or in the pinned Mathlib. So
  $\mathcal L(\eta)|_{X_{s_i}}\cong\mathcal O(d)$ is proved only on global
  sections (the binary forms of degree $d$ above); the Plücker coordinates
  pulled back to $\mathrm{Fl}_n$ are identified with a basis of
  $H^0(\mathrm{Fl}_n,\mathcal L(-\varpi_k))$
  (`Plucker.pluckerSectionBasis_apply`), but the pullback of $\mathcal O(1)$
  is not identified with $\mathcal L(-\varpi_k)$; and $X_S$ is not described
  as the multi-$\mathrm{Proj}$ of its section ring.
- The product in the section ring. `PointModel.geometricSectionRingEquiv` is
  an isomorphism of algebras over every algebraically closed field of
  characteristic zero, but the statement that it matches the multiplication
  of sections `sectionsMul` with the product of the quotient of the
  flag-minor algebra is made only over $\mathbb C$
  (`PointModel.geometricSectionRingEquiv_symm_of_mul_of`).
- The rank-one functor on higher-dimensional modules. It is compared with
  global sections only for characters; for instance
  $H_{s_i}\bigl(H^0(X_w,\mathcal L(\eta))\bigr)\cong H^0(X_{s_iw},\mathcal L(\eta))$
  for $s_iw>w$ is not formalized, and only the corresponding character
  recurrences are proved.

## Standard results proved here

The paper relies on four bodies of standard results, and each is proved here by
a library of its own. The three cited for Theorems 1.4 and 5.3 are stated as
Lean propositions in [Schubert/RS/Statements/](Schubert/RS/Statements). Some
intermediate theorems take one of them as an explicit hypothesis;
[Main/Unconditional.lean](Schubert/RS/Main/Unconditional.lean) applies the
proofs to them, and the audit prints every signature. The last row is the theory
of flag varieties, Schubert varieties, line bundles and Demazure modules behind
Corollary 1.2, which is stated and proved directly for the objects defined in
the flag-variety library.

| Result | Source | Proof | Library |
| --- | --- | --- | --- |
| [`QuiverSaturation`](Schubert/RS/Statements/QuiverSaturation.lean) | H. Derksen, J. Weyman, Semi-invariants of quivers and saturation for Littlewood-Richardson coefficients, J. Amer. Math. Soc. 13 (2000); in the form for multiplicities in the coordinate ring: V. Baldoni, M. Vergne, M. Walter, arXiv:1901.07194, Section 8. | `quiverSaturation_holds` | [`Schubert/QuiverInvariants/`](Schubert/QuiverInvariants) |
| [`PolyTimeRationalFeasibility`](Schubert/RS/Statements/PolyTimeRationalFeasibility.lean) | L. G. Khachiyan, A polynomial algorithm in linear programming, Dokl. Akad. Nauk SSSR 244 (1979); E. Tardos, A strongly polynomial algorithm to solve combinatorial linear programs, Oper. Res. 34 (1986). | `polyTimeRationalFeasibility_holds` | [`Schubert/LinearProgramming/`](Schubert/LinearProgramming) |
| [`GLCharacterMultiplicity`](Schubert/RS/Statements/GLCharacterMultiplicity.lean) | Complete reducibility, characters of irreducible polynomial representations, and Schur's lemma: W. Fulton, J. Harris, Representation Theory, Lectures 6 and 15; R. Stanley, Enumerative Combinatorics 2, Appendix 2, Theorem A2.4. | `glCharacterMultiplicity_holds` | [`Schubert/GLRep/`](Schubert/GLRep) |
| Flag varieties, Schubert varieties, line bundles, Borel–Weil and Demazure modules (Corollary 1.2) | J. C. Jantzen, Representations of Algebraic Groups, 2nd ed., Part II; P. Polo, Variétés de Schubert et excellentes filtrations, Astérisque 173–174 (1989); V. Lakshmibai, K. N. Raghavan, Standard Monomial Theory (2008); W. Fulton, Flags, Schubert polynomials, degeneracy loci, and determinantal formulas, Duke Math. J. 65 (1992). | `FlagVarieties.PointModel.sectionsRestrict_surjective`, `FlagVarieties.borelWeil_ratIrrep`, `FlagVarieties.nonempty_sectionDemazureEquiv_ratIrrep` | [`Schubert/FlagVarieties/`](Schubert/FlagVarieties), [`Schubert/Demazure/`](Schubert/Demazure), [`Schubert/GLRep/`](Schubert/GLRep), [`Schubert/TypeA/`](Schubert/TypeA) |

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
files, then recompiles all **1303 local Lean modules** in dependency
order, and exits with a nonzero status if a module fails. With three jobs the
full build takes about three hours on a laptop.

To resume an interrupted build, or to check that every module was compiled
from the current sources:

```text
python build.py --jobs 3 --resume
python build.py --check
```

A standard `lake build` target is also configured.

The audit prints the main theorem signatures, with their hypotheses, and their
transitive axiom dependencies, including those of the flag-variety library
listed above. The expected axioms are only `propext`, `Classical.choice`, and
`Quot.sound`.

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
  theorems of Theorem 1.1, Corollary 1.3 and the algebraic model of
  Corollary 1.2.
- `Schubert/RS/Geometric/`: Corollary 1.2 for the modules of global sections
  on Schubert varieties, and their identification with the algebraic model.
- `Schubert/RS/`: keys, atoms, duality, and coefficient extraction.
- `Schubert/RS/Window/`: the rational extraction formula.
- `Schubert/RS/Hall/`: the Hall polynomial extraction of Section 3 for general
  Hall triples (Lemmas 3.1 and 3.8, Definition 3.9, Proposition 3.11).
- `Schubert/RS/BModules/`, `Schubert/RS/SchubertUnions/`,
  `Schubert/RS/Filtrations/`: modules for the Borel subalgebra, sums of
  Demazure modules, and filtrations (the algebraic model of Corollary 1.2).
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
- `Schubert/FlagVarieties/`: the flag scheme and its foundations
  (`Foundations/`), Schubert, opposite Schubert and Richardson varieties, line
  bundles and their sections, normality, Bruhat cells, and the Plücker
  embedding; part of the flag-variety library.
- `Schubert/Demazure/`: flag minors, Demazure modules, keys and atoms, and
  the Joseph–Polo presentation; part of the flag-variety library.
- `Schubert/GLRep/`: polynomial and rational representations of general
  linear groups and their Levi groups in characteristic zero, and rational
  representations of the Borel subgroup; part of the flag-variety library.
- `Schubert/LinearProgramming/`: polynomial-time rational feasibility of
  systems of linear inequalities.
- `Schubert/QuiverInvariants/`: semi-invariants of quivers, Schofield's
  formula and the Derksen–Weyman saturation theorem.
- `Schubert/RS/JosephPolo/`, `Schubert/RS/PBW/`,
  `Schubert/RS/Representation/`: presentation, character-formula and PBW
  proofs.
- `Schubert/TypeA/`: permutations, the Bruhat order and divided differences;
  part of the flag-variety library.
- `vendor/complexitylib/`: 197 vendored source files of complexitylib.
- `FLAG_MODULE_MANIFEST.json`: the version, folders and file hashes of the
  flag-variety library.
- `docs/STATEMENTS.md`: the statements of the paper and their Lean
  counterparts.
- `provenance/`: source inventory and verification records.

## Attribution and licensing

This repository is licensed under the [Apache License 2.0](LICENSE), except
for the third-party files described below. Redistributions must retain the
[NOTICE](NOTICE) file. If you use or adapt this code, please cite the paper
([arXiv:2609.28169](https://arxiv.org/abs/2609.28169)) and this repository;
citation metadata is in [CITATION.cff](CITATION.cff).

[GrinbergCauchyBinet.lean](Schubert/RS/JosephPolo/GrinbergCauchyBinet.lean)
and its copy in the flag-variety library,
[Demazure/JosephPolo/GrinbergCauchyBinet.lean](Schubert/Demazure/JosephPolo/GrinbergCauchyBinet.lean),
contain adapted third-party material under **CC BY-NC 4.0** and are not
covered by the Apache License. Their copyright notices, source attribution,
and adjacent license files
([Schubert/RS/JosephPolo/Grinberg.LICENSE](Schubert/RS/JosephPolo/Grinberg.LICENSE),
[Schubert/Demazure/JosephPolo/Grinberg.LICENSE](Schubert/Demazure/JosephPolo/Grinberg.LICENSE))
are retained; a copy of the flag-variety library carries this file under the
same terms. The files in [vendor/complexitylib](vendor/complexitylib) are
unmodified sources of complexitylib under the Apache License 2.0, with its
license in [vendor/complexitylib/LICENSE](vendor/complexitylib/LICENSE). See
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).

Downloaded dependencies retain their own licenses.
