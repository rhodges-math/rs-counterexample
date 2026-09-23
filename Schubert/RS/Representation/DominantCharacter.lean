import Schubert.RS.PresentationCharacter
import Schubert.RS.Representation.Dominant

namespace Schubert.RS.Representation
noncomputable section

theorem jpTorus_dominant_scalar {n : ℕ} (u : Fin n → ℕ) (hu : Antitone u)
    (hpbw : HasOrderedPBWBasis n) (t : DiagonalTorus n) (q : PresentationQuotient u) :
    jpTorusRepresentation u t q = weightScalar u t • q := by
  refine Submodule.Quotient.induction_on (jpLeftIdeal u) q ?_
  intro a
  rw [dominant_mk_eq u hu hpbw a, map_smul, jpTorus_generator, smul_comm]

theorem scalar_torusWeightSpace_eq_top {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : DiagonalTorus n →* Module.End ℂ E) (v : Weight n)
    (hρ : ∀ t x, ρ t x = integerWeightScalar v t • x) : torusWeightSpace ρ v = ⊤ := by
  ext x
  simp only [Submodule.mem_top, iff_true]
  exact fun t => hρ t x

theorem scalar_torusWeightSpace_eq_bot {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : DiagonalTorus n →* Module.End ℂ E) (v z : Weight n) (hvz : z ≠ v)
    (hρ : ∀ t x, ρ t x = integerWeightScalar v t • x) : torusWeightSpace ρ z = ⊥ := by
  apply le_antisymm
  · intro x hx
    change x = 0
    by_contra hn
    apply hvz
    apply integerWeightScalar_injective
    funext t
    exact smul_left_injective ℂ hn ((hx t).symm.trans (hρ t x))
  · exact bot_le

/-- The dominant character base for an independently supplied actual target.
Only PBW and the natural JP input are used; DCF is not a premise. -/
theorem dominant_target_weight_finrank {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    [Module (Enveloping n) E] [IsScalarTower ℂ (Enveloping n) E]
    (u : Composition n) (hu : Antitone u) (hpbw : HasOrderedPBWBasis n)
    (ρ : DiagonalTorus n →* Module.End ℂ E) (ξ : E) (hJP : HasJosephPoloPresentation u ρ ξ)
    (z : Weight n) :
    FiniteDimensional ℂ (torusWeightSpace ρ z) ∧
      Module.finrank ℂ (torusWeightSpace ρ z) = if z = (fun i => (u i : ℤ)) then 1 else 0 := by
  classical
  obtain ⟨e, hξ, he⟩ := hJP
  let ec : E ≃ₗ[ℂ] ℂ := (e.restrictScalars ℂ).symm.trans (dominantQuotientEquiv u hu hpbw)
  letI : FiniteDimensional ℂ E := Module.Finite.equiv ec.symm
  have hs : ∀ t x, ρ t x = integerWeightScalar (fun i => (u i : ℤ)) t • x := by
    intro t x
    obtain ⟨q, rfl⟩ := e.surjective x
    rw [← he, jpTorus_dominant_scalar u hu hpbw]
    rw [integerWeightScalar_nat]
    exact (e.restrictScalars ℂ).map_smul _ _
  refine ⟨inferInstance, ?_⟩
  split_ifs with hz
  · subst z
    rw [scalar_torusWeightSpace_eq_top _ _ hs]
    have hr : Module.finrank ℂ E = 1 := by simpa using ec.finrank_eq
    simpa using hr
  · rw [scalar_torusWeightSpace_eq_bot _ _ _ hz hs]
    simp

/-- The Demazure character property in the dominant base case, for a target
module related to the presentation quotient by the Joseph-Polo isomorphism. -/
theorem dominant_hasDemazureCharacter {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    [Module (Enveloping n) E] [IsScalarTower ℂ (Enveloping n) E]
    (u : Composition n) (hu : Antitone u) (hpbw : HasOrderedPBWBasis n)
    (ρ : DiagonalTorus n →* Module.End ℂ E) (ξ : E) (hJP : HasJosephPoloPresentation u ρ ξ) :
    HasDemazureCharacter u ρ := by
  classical
  intro z
  obtain ⟨hf, hr⟩ := dominant_target_weight_finrank u hu hpbw ρ ξ hJP z
  refine ⟨hf, ?_⟩
  rw [hr, key_of_antitone u hu, compositionMonomial, toLaurent_monomial]
  have he : exponentWeight (Finsupp.equivFunOnFinite.symm u) = (fun i => (u i : ℤ)) := by
    funext i
    simp [exponentWeight]
  simp only [he, AddMonoidAlgebra.coeff_single]
  change ((if z = (fun i => (u i : ℤ)) then 1 else 0 : ℕ) : ℤ) =
    (Finsupp.single (fun i => (u i : ℤ)) (1 : ℤ)) z
  rw [Finsupp.single_apply]
  by_cases hz : z = (fun i => (u i : ℤ))
  · subst z
    norm_num
  · simp only [if_neg hz, if_neg (Ne.symm hz), Nat.cast_zero]

end
end Schubert.RS.Representation
