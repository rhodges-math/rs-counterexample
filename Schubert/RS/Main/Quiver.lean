import Schubert.RS.Quiver.Polytope.Counts
import Schubert.RS.Quiver.Polytope.Positivity
import Schubert.RS.Quiver.Polytope.Scaling
import Schubert.RS.Quiver.Polytope.Bounded
import Schubert.RS.Quiver.TwoSource
import Schubert.RS.Quiver.Density.Count
import Schubert.RS.Statements.GLCharacterMultiplicity
import Schubert.RS.Statements.QuiverSaturation

/-!
# Endpoints: quiver triples (Theorem 1.4, Corollary 1.5, Theorem 5.3, Proposition 5.8)

Namespaces `Schubert.RS.Quiver` and `Schubert.RS.Quiver.Flat` (the polytope). A triple of lists
`a, b, c` is read as weak compositions of length `n = c.length` (`listComp`, entries beyond a list
are `0`). The canonical partition of the triple is `canonicalPart a b c`, its quiver with
`N = max c` is `canonicalQuiver a b c`, and the weights `λ^{(p)}` are `canonicalWeight a b c`
(as dominant weights, `canonicalDominantWeight`).

## Theorem 1.4 (`thm:intro-quiver-polytope`)

* The polytope `P(a, b, c) ⊆ ℝ^M`: `quiverPolytope a b c`, a system of integer linear
  inequalities (`IntPolyhedron`); its real points are `(quiverPolytope a b c).points ℝ` and its
  integer points `(quiverPolytope a b c).intPoints`. Its size: `quiverPolytope_dim`,
  `quiverPolytope_rows_length`; coefficients in `{−1, 0, 1}` (`quiverPolytope_coeff_mem`);
  right-hand sides `0` or `±(c_x − a_x − b_x)` (`quiverPolytope_rhs_mem`,
  `quiverPolytope_abs_rhs_le`).
* The counting identity
  `[𝒜_c](κ_a κ_b) = dim Hom_{L_I}(⊗_p V_p^{λ^{(p)}}, R_Q) = #(P(a, b, c) ∩ ℤ^M)`:
  `quiverTheorem_counts`, which takes `GLCharacterMultiplicity` as a hypothesis, together with
  the finiteness of `P(a, b, c) ∩ ℤ^M` and of the Hom space (`finiteDimensional_canonicalHom`).
  The outer equality and the finiteness without hypothesis: `quiverPolytope_card`
  (from `atomCoefficient_eq_card_intPoints`, `finite_intPoints`).
* Boundedness: `quiverPolytope_bounded` (for every triple of lists).
* `[𝒜_c](κ_a κ_b) > 0 ⇔ P(a, b, c) ≠ ∅`, with `QuiverSaturation` as a hypothesis:
  `quiverCoefficient_pos_iff_nonempty` (a real point, `P ⊆ ℝ^M`) and
  `quiverCoefficient_pos_iff_ratFeasible` (a rational point). The direction `⇒` without
  hypothesis: `nonempty_of_quiverCoefficient_pos`. The step that uses the hypothesis, passing
  positivity from `N λ` to `λ`: `ForwardQuiver.multiplicity_pos_of_nsmul`, which takes
  `QuiverSaturation` as a hypothesis.
* Without the saturation hypothesis: `P(a, b, c) ≠ ∅` iff `[𝒜_{N c}](κ_{N a} κ_{N b}) > 0` for some
  `N ≥ 1` (`quiverPolytope_nonempty_iff_exists_nsmul_pos`, and with a rational point
  `quiverPolytope_ratFeasible_iff_exists_nsmul_pos`). The dilated triple is a quiver triple with
  the same canonical partition and quiver (`isQuiverTriple_nsmul`, `canonicalPartition_nsmul`,
  `quiverOf_nsmul`), and its coefficient counts the integer points of the dilate
  `N · P(a, b, c)` (`atomCoefficient_nsmul_eq_card`).
* The algorithms of Theorem 1.4 are recorded in `Schubert/RS/Main/Complexity.lean`.

## Corollary 1.5 (`cor:intro-quiver-density`)

Namespace `Schubert.RS.Quiver.Density`: `card_positiveQuiverTriples_isTheta`
(`#𝒬_n^+(H) = Θ(H^{3n−1})` for `n ≥ 4`) and `positiveQuiverTriples_proportion`.

## Definition 5.1 and Theorem 5.3 (`def:quiver-triple`, `thm:quiver-coefficient`)

* Quiver triples and partitions: `IsQuiverTriple`, `IsQuiverPartition`; the canonical partition
  `canonicalPartition`, with `isQuiverTriple_iff_canonical`; independence of `N ≥ max c`:
  `isQuiverPartition_iff_of_le`.
* The quiver and the weights: `quiverOf`, `leviWeight`, `leviDominantWeight`.
* Theorem 5.3, `[𝒜_c](κ_a κ_b) = dim Hom_{L_I}(⊗_p V_p^{λ^{(p)}}, R_Q)`:
  `atomCoefficient_eq_finrank_hom`, which takes `GLCharacterMultiplicity` as a hypothesis; the
  Hom space is finite-dimensional (`finiteDimensional_quiverHom`). In characters, without
  hypothesis: `atomCoefficient_eq_multiplicity`. Nonnegativity: `atomCoefficient_nonneg`.
* For every forward quiver, `dim Hom` as the multiplicity in characters:
  `ForwardQuiver.finrank_intertwiningMap_coordRep_eq_multiplicity_of_gl`, which takes
  `GLCharacterMultiplicity` as a hypothesis.

## Proposition 5.8 (`prop:quiver-two-source`)

`twoSource_isQuiverPartition`, `twoSource_eq_weylProjector` ((5.10), with the Weyl projector
(5.7) at `(ν₁, ν₂)`), `twoSource_eq_kostka` (the tableau count), `twoSource_pos_iff` ((5.11)). The
last sentence, computing the coefficient in time polynomial in `n + |a| + |b| + |c|`:
`Algorithms.twoSource_coefficient_computable`, recorded in `Schubert/RS/Main/Complexity.lean`.
-/
