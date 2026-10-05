import Schubert.GLRep.Borel.Torus
import Schubert.GLRep.Borel.Basic
import Schubert.GLRep.Borel.Character
import Schubert.GLRep.Borel.Filtration
import Schubert.GLRep.Borel.LocalCoefficients
import Schubert.GLRep.Borel.Induced
import Schubert.GLRep.Borel.Regular
import Schubert.GLRep.Borel.Evaluation
import Schubert.GLRep.Borel.SpecialLinear
import Schubert.GLRep.Borel.GLRegular
import Schubert.GLRep.Borel.Frobenius
import Schubert.GLRep.Borel.DetTwist
import Schubert.GLRep.Borel.Dual
import Schubert.GLRep.Borel.IndTwist
import Schubert.GLRep.Borel.Vanishing
import Schubert.GLRep.Borel.MatrixCoeff
import Schubert.GLRep.Borel.Generation
import Schubert.GLRep.Borel.Comodule
import Schubert.GLRep.Borel.BorelStabilityDifferential
import Schubert.GLRep.Borel.BorelLie
import Schubert.GLRep.Borel.BorelComodule
import Schubert.GLRep.Borel.BorelRational
import Schubert.GLRep.Borel.BorelLieDual
import Schubert.GLRep.Borel.BorelDual

/-!
# Rational representations of the Borel subgroup of `GL_n`

This file imports the whole of `Schubert/GLRep/Borel` and indexes its main results.

## The Borel subgroup and its rational representations

* `GLRep.borel K n` (invertible upper-triangular matrices), its diagonal `GLRep.borelDiag`, torus
  `GLRep.borelTorus`, unipotent radical `GLRep.borelUnipotent`, characters `GLRep.borelChar`, the
  Borel subgroup of `SL_n` `GLRep.borelSL` and the scalar matrices `GLRep.borelScalar`.
* Regular functions on `B` (`GLRep.borelFunctions`) and rational representations
  (`GLRep.IsRationalBorelRep`); restriction from `GL_n` (`GLRep.IsRationalRep.restrictBorel`);
  the one-dimensional representations `K_η` (`GLRep.borelCharRep`).
* Rational representations of a split torus are those with Laurent matrix coefficients
  (`GLRep.isRationalTorusRep_iff_hasCoeffsIn_laurentFunctions`).

## Weights and characters

* `GLRep.borelWeightSpace`, `GLRep.borelCharacter` (`∑ dim W_μ x^μ`), trace formula and
  uniqueness, invariance under equivalence, additivity on subrepresentations and quotients
  (`GLRep.IsRationalBorelRep.borelCharacter_eq_add`), products, tensor products, twists.
* Filtrations (`GLRep.RepFiltration`, `GLRep.HasFiltrationBy`) and additivity of characters along
  them (`GLRep.RepFiltration.borelCharacter_eq_sum`).
* Central characters and `B_SL`-filtrations (`GLRep.HasCentralCharacter`,
  `GLRep.HasCentralCharacter.toRepFiltration`, `GLRep.borelCharacter_eq_of_equiv_borelSL`).

## Induction and the coordinate ring

* Semi-invariants of commuting actions (`GLRep.semiInvariants`, `GLRep.semiInvariantSubrep`), the
  induced representation on functions and Frobenius reciprocity (`GLRep.indRep`,
  `GLRep.indFrobeniusEquiv`).
* The coordinate ring `𝒪(GL_n)` (`FlagVarieties.GLCoord`), left and right translations
  (`GLRep.leftTranslHom`, `GLRep.rightTranslHom`), evaluation (`GLRep.glEval`) and vanishing ideals
  (`GLRep.vanishingIdeal`).
* Representations with regular matrix coefficients (`GLRep.HasLocalCoeffsIn`); the left regular
  representation has them (`GLRep.hasLocalCoeffsIn_leftRegularRep_borel`,
  `GLRep.hasLocalCoeffsIn_leftRegularRep`); rational = regular coefficients for `GL_n`
  (`GLRep.isRationalRep_iff_hasCoeffsIn_glRegularFunctions`).
* **Sections of line bundles in the ring model**: for an ideal `I ⊆ 𝒪(GL_n)` stable under left and
  right translation by `B`, the semi-invariants `(𝒪(GL_n)/I)^{(B, η)}` (`GLRep.borelSemiInvariants`)
  with the action of `B` by left translation (`GLRep.borelSemiInvariantRep`), rational when
  finite-dimensional (`GLRep.isRationalBorelRep_borelSemiInvariantRep`), with central character
  `∑ ηᵢ` (`GLRep.hasCentralCharacter_borelSemiInvariantRep`), and restriction maps
  (`GLRep.borelSemiInvariantRestrict`); the induced representation `ind_B^G(η)` of `GL_n(K)`
  (`GLRep.indBorelRep`); twisting by powers of the determinant
  (`GLRep.borelSemiInvariantDetTwist`).
* Over an infinite field `𝒪(GL_n)` is the algebra of regular functions on `GL_n(K)`
  (`GLRep.glEvalEquiv`), and **Frobenius reciprocity** holds for rational representations:
  `Hom_G(V, ind_B^G(η)) ≃ Hom_B(V, K_η)` (`GLRep.indBorelFrobeniusEquiv`).

## Duals

* The inverse-transpose automorphism `θ(g) = (g⁻¹)ᵀ` (`GLRep.inverseTranspose`) negates weights
  (`GLRep.ratCharacter_comp_inverseTranspose`, with `GLRep.laurentNeg : x^μ ↦ x^{−μ}`); duals of
  rational representations are rational with negated character
  (`GLRep.IsRationalRep.ratCharacter_dual`), duals of irreducibles are irreducible
  (`GLRep.isIrreducible_dual`), and `ρ ∘ θ ≅ ρ^∨` for irreducible rational `ρ`
  (`GLRep.nonempty_equiv_comp_inverseTranspose_dual`); twists and duals commute
  (`GLRep.dual_scaledRep`).
* Twisting `ind_B^G(η)` by `det^c` gives `ind_B^G(η + c·1)` (`GLRep.indBorelDetTwist`).
* **Vanishing**: over an infinite field, `ind_B^G(η) = 0` unless `η` is weakly increasing
  (`GLRep.indBorelSubrep_eq_bot`), by the rank-one factorization
  `GLRep.transvectionGL_lower_eq`.
* Matrix coefficients `g ↦ φ(ρ(g) v)` as regular functions (`GLRep.matrixCoeff`), the map
  `V^∨ → ind_B^G(η)` of a `B`-eigenvector (`GLRep.dualToInducedRep`), and orbit spans
  `⟨ρ(g) v : g ∈ Z⟩` (`GLRep.orbitSpan`, `GLRep.orbitSubrep`) with
  `GLRep.matrixCoeff_mem_vanishingIdeal_iff`.
* `B` is generated by the diagonal torus and the upper transvections (`GLRep.borel_induction`).

## Comodules

* Rational representations of `GL_n(K)` are comodules over Tau Ceti's `𝒪(GL_n)`
  (`GLRep.rationalComodule`, `GLRep.contract_rationalComodule`), comodules give representations
  (`GLRep.comoduleRep`), and morphisms correspond (`GLRep.homOfIntertwining`, `GLRep.rationalHom`).
* Over `𝒪(B)` (Tau Ceti's upper-triangular coordinate Hopf algebra, `GLRep.borelHopf`): points
  separate (`GLRep.borelHopf_ext`), restrictions of rational `GL_n`-representations are
  `𝒪(B)`-comodules with point action `ρ|_B` (`GLRep.borelComodule`,
  `GLRep.contract_borelComodule`), and `B`-stable subspaces are subcomodules
  (`GLRep.borelSubcomodule`, `GLRep.borelSubcomoduleOfStable`).
* **Rational representations of `B(K)` are the `𝒪(B)`-comodules** (`K` infinite): the points form a
  convolution submonoid (`GLRep.borelPointHom`), comodules give representations
  (`GLRep.borelComoduleRep`, rational when finite-dimensional:
  `GLRep.isRationalBorelRep_borelComoduleRep`), every rational representation is a comodule
  (`GLRep.IsRationalBorelRep.comodule`, `GLRep.IsRationalBorelRep.contract_comodule`), and the two
  constructions are inverse (`GLRep.rationalBorelRepEquivComodule`).
* Duals: the antipode of `𝒪(B)` is inversion on points (`GLRep.borelPoint_antipode`), the dual
  comodule has the dual point action (`GLRep.borelComoduleRep_dual`), and the comodule of the dual
  of a rational representation is the dual comodule (`GLRep.IsRationalBorelRep.comodule_dual`).

## `B`-stability through the differential (restrictions of `GL_n`-representations)

* A subspace of a polynomial (or rational) representation is `B`-stable iff it is stable under
  the torus and `dρ(E_ab)`, `a < b` (`GLRep.IsPolynomialRep.forall_borel_mem_iff`,
  `GLRep.IsRationalRep.forall_borel_mem_iff`); likewise for maps
  (`GLRep.IsPolynomialRep.forall_borel_intertwining_iff`).

## `B`-stability through the differential (all rational representations of `B`)

* Along `u_ab(t) = 1 + tE_ab` a rational representation of `B` is an exponential
  `Σ t^k/k! D_ab^k` (`GLRep.IsRationalBorelRep.exists_rho_upperTransvection_eq`,
  `GLRep.IsRationalBorelRep.borelLie`); `B`-stable subspaces and `B`-maps are those compatible with
  the torus and the `D_ab` (`GLRep.IsRationalBorelRep.forall_mem_iff`,
  `GLRep.IsRationalBorelRep.forall_intertwining_iff`); `ρ(t) D_ab ρ(t)⁻¹ = (t_a/t_b) D_ab`
  (`GLRep.IsRationalBorelRep.conj_borelLie`); on restrictions of `GL_n`-representations `D_ab` is
  GLRep's `dρ(E_ab)` (`GLRep.IsRationalBorelRep.borelLie_restrictBorel`); naturality
  (`GLRep.IsRationalBorelRep.borelLie_comp_of_intertwining`), subrepresentations and duals
  (`GLRep.IsRationalBorelRep.dual`, `GLRep.IsRationalBorelRep.borelLie_dual_apply`).
-/
