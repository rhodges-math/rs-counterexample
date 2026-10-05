import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.Ideal.Span

/-!
# Equality in a finite positive-root coefficient window

All exponents are nonnegative. Consequently multiplication cannot bring an
excluded high degree back into the window. This file proves that step without
any representation-theoretic input.
-/

namespace Demazure

noncomputable section
variable {σ : Type*}

/-- The two power series have the same coefficients in all degrees `d ≤ β`. -/
def TruncEq (β : σ →₀ ℕ) (f g : MvPowerSeries σ ℤ) : Prop :=
  ∀ d ≤ β, MvPowerSeries.coeff d f = MvPowerSeries.coeff d g

namespace TruncEq

theorem refl (β : σ →₀ ℕ) (f : MvPowerSeries σ ℤ) : TruncEq β f f :=
  fun _ _ => rfl

theorem symm {β : σ →₀ ℕ} {f g : MvPowerSeries σ ℤ} (h : TruncEq β f g) :
    TruncEq β g f := fun d hd => (h d hd).symm

theorem trans {β : σ →₀ ℕ} {f g h : MvPowerSeries σ ℤ}
    (hfg : TruncEq β f g) (hgh : TruncEq β g h) : TruncEq β f h :=
  fun d hd => (hfg d hd).trans (hgh d hd)

theorem add {β : σ →₀ ℕ} {f f' g g' : MvPowerSeries σ ℤ}
    (hf : TruncEq β f f') (hg : TruncEq β g g') :
    TruncEq β (f + g) (f' + g') := by
  intro d hd
  simp only [map_add, hf d hd, hg d hd]

theorem mul {β : σ →₀ ℕ} {f f' g g' : MvPowerSeries σ ℤ}
    (hf : TruncEq β f f') (hg : TruncEq β g g') :
    TruncEq β (f * g) (f' * g') := by
  classical
  intro d hd
  simp only [MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have he : p.1 + p.2 = d := Finset.mem_antidiagonal.mp hp
  have h₁ : p.1 ≤ β := le_trans (he ▸ le_add_right le_rfl) hd
  have h₂ : p.2 ≤ β := le_trans (he ▸ le_add_left le_rfl) hd
  rw [hf _ h₁, hg _ h₂]

theorem monomial_mul_zero (β d : σ →₀ ℕ) (z : ℤ)
    (f : MvPowerSeries σ ℤ) (h : ¬d ≤ β) :
    TruncEq β (MvPowerSeries.monomial d z * f) 0 := by
  intro e he
  rw [MvPowerSeries.coeff_monomial_mul, ite_eq_right (fun hde => h (hde.trans he))]
  simp

end TruncEq

/-- Series invisible inside the coefficient window form an ideal. -/
def truncationIdeal (β : σ →₀ ℕ) : Ideal (MvPowerSeries σ ℤ) where
  carrier := {f | TruncEq β f 0}
  zero_mem' := TruncEq.refl _ _
  add_mem' := by
    intro f g hf hg
    simpa using hf.add hg
  smul_mem' := by
    intro f g hg
    simpa using (TruncEq.refl β f).mul hg

theorem monomial_mem_truncationIdeal (β d : σ →₀ ℕ) (z : ℤ) (h : ¬d ≤ β) :
    MvPowerSeries.monomial d z ∈ truncationIdeal β := by
  have hh := TruncEq.monomial_mul_zero β d z 1 h
  simpa [truncationIdeal] using hh

/-- Every combination of excluded generators remains invisible. -/
theorem span_monomials_le_truncationIdeal (β : σ →₀ ℕ) (S : Set (σ →₀ ℕ))
    (h : ∀ d ∈ S, ¬d ≤ β) :
    Ideal.span ((fun d => MvPowerSeries.monomial d (1 : ℤ)) '' S) ≤ truncationIdeal β := by
  apply Ideal.span_le.mpr
  rintro _ ⟨d, hd, rfl⟩
  exact monomial_mem_truncationIdeal β d 1 (h d hd)

end
end Demazure
