import Schubert.RS.LinearWindowCount
import Schubert.RS.FullWeightSupport
import Schubert.RS.LaurentPrefixSupport

/-! Initial coefficients and prefix support under the Joseph-Polo,
Demazure character, and PBW hypotheses. -/

namespace Schubert.RS
noncomputable section
open Representation
variable {n : ℕ}

theorem monomialDegree_eq_zero_iff (a : PositiveRoot n → ℕ) :
    monomialDegree a = 0 ↔ a = 0 := by
  constructor
  · intro h
    funext r
    have hb := degree_fiber_bound
      (fun r : PositiveRoot n => rootDegree r.val.1 r.val.2)
      (fun r => rootFirstCut r.val.1 r.val.2 r.property)
      (fun r => rootDegree_first r.val.1 r.val.2 r.property) 0 a h r
    simpa using Nat.eq_zero_of_le_zero hb
  · rintro rfl
    simp [monomialDegree]

theorem ascentDegreeFiber_zero_card (u : Composition n) :
    Fintype.card (AscentDegreeFiber u 0) = 1 := by
  classical
  have hz : extendAscentPowers u 0 = 0 := by
    funext r
    simp [extendAscentPowers]
  let z : AscentDegreeFiber u 0 := ⟨0, by rw [hz]; simp [monomialDegree]⟩
  letI : Unique (AscentDegreeFiber u 0) :=
    { default := z
      uniq := by
        intro a
        apply Subtype.ext
        apply extendAscentPowers_injective u
        rw [hz]
        exact (monomialDegree_eq_zero_iff _).mp a.property }
  exact Fintype.card_unique

variable {E : Type*} [AddCommGroup E] [Module ℂ E]
  [Module (Enveloping n) E] [IsScalarTower ℂ (Enveloping n) E]

theorem key_initial_coefficient (u : Composition n)
    (ρ : DiagonalTorus n →* Module.End ℂ E) (ξ : E)
    (hJP : HasJosephPoloPresentation u ρ ξ) (hDCF : HasDemazureCharacter u ρ)
    (hpbw : HasOrderedPBWBasis n) :
    (toLaurent (key u)).coeff (fun i => (u i : ℤ)) = 1 := by
  have hβ : ∀ r : PositiveRoot n, u r.val.1 < u r.val.2 →
      ¬ jpExponent u r • rootDegree r.val.1 r.val.2 ≤ 0 := by
    intro r hr
    apply root_power_outside_window r.val.1 r.val.2 r.property
    simp [jpExponent]
  have h := key_coefficient_eq_ascent_count u ρ ξ hJP hDCF hpbw 0 0 le_rfl hβ
  simpa [weightOfRootDegree, rootWeight_zero, ascentDegreeFiber_zero_card] using h

theorem key_prefixSupported (u : Composition n)
    (ρ : DiagonalTorus n →* Module.End ℂ E) (ξ : E)
    (hJP : HasJosephPoloPresentation u ρ ξ) (hDCF : HasDemazureCharacter u ρ)
    (hpbw : HasOrderedPBWBasis n) :
    PrefixSupported (fun i => (u i : ℤ)) (toLaurent (key u)) := by
  intro w hw
  obtain ⟨d, rfl⟩ := key_support_positive_root_cone u ρ ξ hJP hDCF hpbw w hw
  exact prefixLE_add_rootWeight _ d

end
end Schubert.RS
