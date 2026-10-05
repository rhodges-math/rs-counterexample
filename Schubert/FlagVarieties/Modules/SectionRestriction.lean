import Schubert.FlagVarieties.LineBundle.BorelRep
import Schubert.FlagVarieties.Schubert.PreimageLattice

/-!
# Restriction of sections to a smaller closed subscheme

For closed subschemes `X' ⊆ X ⊆ Flₙ` over a commutative ring `R` (ideal sheaves `I ≤ I'`), the
preimage ideals satisfy `J ≤ J'` (`FlagVarieties.preimageIdeal_mono`), and the quotient map
`𝒪(GLₙ)/J → 𝒪(GLₙ)/J'` sends `(B, η)`-semi-invariants to `(B, η)`-semi-invariants
(`FlagVarieties.semiInvariantsRestrict`), compatibly with left translation by `B(R)`.

* **`FlagVarieties.sectionsRestrictHom`**: the restriction
  `H⁰(X, 𝓛(η)) → H⁰(X', 𝓛(η))`, transported through `sectionsEquivSemiInvariants`, as an
  intertwining map of the representations `sectionsRep` of `B(R)`.
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry
open scoped TensorProduct

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

/-! ### Semi-invariants -/

section SemiInvariants

variable {J J' : Ideal (GLCoord R n)} (h : J ≤ J')

/-- The defect `f ↦ ρ(f) - f ⊗ η⁻¹` for `J'` is the image of the defect for `J`. -/
theorem semiInvariantDefect_factor (η : Fin n → ℤ) (f : GLCoord R n) :
    semiInvariantDefect R n J' η f =
      Algebra.TensorProduct.map (Ideal.Quotient.factorₐ R h) (AlgHom.id R (BorelCoord R n))
        (semiInvariantDefect R n J η f) := by
  rw [semiInvariantDefect_apply, semiInvariantDefect_apply, map_sub, Algebra.TensorProduct.map_tmul]
  congr 1
  change _ = (Algebra.TensorProduct.map (Ideal.Quotient.factorₐ R h)
    (AlgHom.id R (BorelCoord R n))) ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R J)
      (AlgHom.id R (BorelCoord R n))) (rightCoaction R n f))
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp]
  rfl

theorem factor_mem_quotientSemiInvariants (η : Fin n → ℤ) {x : GLCoord R n ⧸ J}
    (hx : x ∈ quotientSemiInvariants R n J η) :
    Ideal.Quotient.factorₐ R h x ∈ quotientSemiInvariants R n J' η := by
  obtain ⟨f, hf, rfl⟩ := hx
  refine ⟨f, ?_, rfl⟩
  have hf' : semiInvariantDefect R n J η f = 0 := hf
  show semiInvariantDefect R n J' η f = 0
  rw [semiInvariantDefect_factor h, hf', map_zero]

/-- **Restriction of semi-invariants**: the quotient map `𝒪(GLₙ)/J → 𝒪(GLₙ)/J'` for `J ≤ J'`. -/
def semiInvariantsRestrict (η : Fin n → ℤ) :
    quotientSemiInvariants R n J η →ₗ[R] quotientSemiInvariants R n J' η :=
  (Ideal.Quotient.factorₐ R h).toLinearMap.restrict fun _ hx =>
      factor_mem_quotientSemiInvariants h η hx

@[simp]
theorem coe_semiInvariantsRestrict (η : Fin n → ℤ) (x : quotientSemiInvariants R n J η) :
    (semiInvariantsRestrict h η x : GLCoord R n ⧸ J') = Ideal.Quotient.factorₐ R h x :=
  rfl

/-- Restriction of semi-invariants commutes with left translation by `B(R)`. -/
def semiInvariantsRestrictHom (hJ : IsLeftTranslStable J) (hJ' : IsLeftTranslStable J')
    (η : Fin n → ℤ) :
    (semiInvariantsRep J hJ η).IntertwiningMap (semiInvariantsRep J' hJ' η) where
  toLinearMap := semiInvariantsRestrict h η
  isIntertwining' b := LinearMap.ext fun x => Subtype.ext <| by
    obtain ⟨x, -⟩ := x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

end SemiInvariants

/-! ### Sections -/

variable (R n)

/-- **Restriction of sections** `H⁰(X, 𝓛(η)) → H⁰(X', 𝓛(η))` for closed subschemes `X' ⊆ X`
(ideal sheaves `I ≤ I'`).

It is the quotient map `(𝒪(GLₙ)/J)^{(B, η)} → (𝒪(GLₙ)/J')^{(B, η)}` of the preimage ideals,
transported through `sectionsEquivSemiInvariants`, and it commutes with the action of `B(R)`
by left translation (`sectionsRep`). -/
def sectionsRestrictHom {I I' : (FlagScheme R n).IdealSheafData} (h : I ≤ I') (η : Fin n → ℤ)
    (hJ : IsLeftTranslStable (preimageIdeal R n I))
    (hJ' : IsLeftTranslStable (preimageIdeal R n I')) :
    (sectionsRep R n I η hJ).IntertwiningMap (sectionsRep R n I' η hJ') where
  toLinearMap := (sectionsEquivSemiInvariants R n I' η).symm.toLinearMap ∘ₗ
    semiInvariantsRestrict (preimageIdeal_mono R n h) η ∘ₗ
        (sectionsEquivSemiInvariants R n I η).toLinearMap
  isIntertwining' b := LinearMap.ext fun s => by
    change (sectionsEquivSemiInvariants R n I' η).symm
        (semiInvariantsRestrict (preimageIdeal_mono R n h) η
        (sectionsEquivSemiInvariants R n I η (sectionsRep R n I η hJ b s))) =
      (sectionsEquivSemiInvariants R n I' η).symm (semiInvariantsRep _ hJ' η b
        (sectionsEquivSemiInvariants R n I' η ((sectionsEquivSemiInvariants R n I' η).symm
          (semiInvariantsRestrict (preimageIdeal_mono R n h) η
              (sectionsEquivSemiInvariants R n I η s)))))
    rw [sectionsEquivSemiInvariants_sectionsRep, LinearEquiv.apply_symm_apply]
    exact congrArg _ ((semiInvariantsRestrictHom (preimageIdeal_mono R n h) hJ hJ' η).isIntertwining
      _ _ b _)

variable {R n}

theorem sectionsEquivSemiInvariants_sectionsRestrictHom {I I' : (FlagScheme R n).IdealSheafData}
    (h : I ≤ I')
    (η : Fin n → ℤ) (hJ : IsLeftTranslStable (preimageIdeal R n I))
    (hJ' : IsLeftTranslStable (preimageIdeal R n I')) (s : sections R n I η) :
    sectionsEquivSemiInvariants R n I' η (sectionsRestrictHom R n h η hJ hJ' s) =
      semiInvariantsRestrict (preimageIdeal_mono R n h) η (sectionsEquivSemiInvariants R n I η s) :=
  LinearEquiv.apply_symm_apply _ _

end FlagVarieties
