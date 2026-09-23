import Schubert.RS.GlobalDuality

/-! Extraction from any atom expansion and the obstruction to a nonnegative one. -/

namespace Schubert.RS
noncomputable section
open Representation
variable {n : ℕ}

def rectangleCoefficientLinear (w : ℕ) (c : Composition n) : Polynomial n →ₗ[ℤ] ℤ where
  toFun := rectangleCoefficient w c
  map_add' f g := by simp [rectangleCoefficient, add_mul]
  map_smul' z f := by
    change (toLaurent (z • f) * toLaurent (key (fun i => w - c i)) * weylFactor n).coeff
      (fun _ => (w : ℤ)) = z • rectangleCoefficient w c f
    rw [map_zsmul, smul_mul_assoc, smul_mul_assoc]
    rfl

/-- Atom positivity means an actual finite nonnegative atom expansion. -/
def AtomPositive (f : Polynomial n) : Prop :=
  ∃ t : Composition n →₀ ℕ, f = t.sum (fun u z => z • atom u)

variable {E : Composition n → Type*}
  [∀ u, AddCommGroup (E u)] [∀ u, Module ℂ (E u)]
  [∀ u, Module (Enveloping n) (E u)] [∀ u, IsScalarTower ℂ (Enveloping n) (E u)]

theorem rectangleCoefficient_expansion
    (ρ : (u : Composition n) → DiagonalTorus n →* Module.End ℂ (E u))
    (ξ : (u : Composition n) → E u)
    (hJP : ∀ u, HasJosephPoloPresentation u (ρ u) (ξ u))
    (hDCF : ∀ u, HasDemazureCharacter u (ρ u)) (hpbw : HasOrderedPBWBasis n)
    (w : ℕ) (c : Composition n) (hc : ∀ i, c i ≤ w) (t : Composition n →₀ ℤ) :
    rectangleCoefficient w c (t.sum (fun u z => z • atom u)) = t c := by
  classical
  change rectangleCoefficientLinear w c (t.sum _) = _
  simp only [Finsupp.sum, map_sum, map_smul]
  change (∑ u ∈ t.support, t u • rectangleCoefficient w c (atom u)) = t c
  simp only [rectangleCoefficient_atom ρ ξ hJP hDCF hpbw w c _ hc, smul_eq_mul]
  by_cases h : c ∈ t.support
  · simp [mul_ite, h]
  · simp [mul_ite, h, Finsupp.notMem_support_iff.mp h]

theorem AtomPositive.rectangleCoefficient_nonneg
    (ρ : (u : Composition n) → DiagonalTorus n →* Module.End ℂ (E u))
    (ξ : (u : Composition n) → E u)
    (hJP : ∀ u, HasJosephPoloPresentation u (ρ u) (ξ u))
    (hDCF : ∀ u, HasDemazureCharacter u (ρ u)) (hpbw : HasOrderedPBWBasis n)
    (w : ℕ) (c : Composition n) (hc : ∀ i, c i ≤ w)
    (f : Polynomial n) (hf : AtomPositive f) : 0 ≤ rectangleCoefficient w c f := by
  classical
  obtain ⟨t, rfl⟩ := hf
  change 0 ≤ rectangleCoefficientLinear w c (t.sum _)
  simp only [Finsupp.sum, map_sum, map_nsmul]
  apply Finset.sum_nonneg
  intro u hu
  change 0 ≤ t u • rectangleCoefficient w c (atom u)
  rw [rectangleCoefficient_atom ρ ξ hJP hDCF hpbw w c u hc]
  split_ifs <;> simp

theorem not_atomPositive_of_negative_rectangle
    (ρ : (u : Composition n) → DiagonalTorus n →* Module.End ℂ (E u))
    (ξ : (u : Composition n) → E u)
    (hJP : ∀ u, HasJosephPoloPresentation u (ρ u) (ξ u))
    (hDCF : ∀ u, HasDemazureCharacter u (ρ u)) (hpbw : HasOrderedPBWBasis n)
    (w : ℕ) (c : Composition n) (hc : ∀ i, c i ≤ w)
    (f : Polynomial n) (hf : rectangleCoefficient w c f < 0) : ¬AtomPositive f := by
  intro hp
  exact (not_le_of_gt hf) (hp.rectangleCoefficient_nonneg ρ ξ hJP hDCF hpbw w c hc f)

end
end Schubert.RS
