import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.Ideal.Span

/-!
# Equality in a finite positive-root coefficient window

All exponents are nonnegative. Consequently multiplication cannot bring an
excluded high degree back into the window. This file proves that step without
any representation-theoretic input.
-/

namespace Schubert.RS

noncomputable section
variable {σ : Type*}

def WindowEq (β : σ →₀ ℕ) (f g : MvPowerSeries σ ℤ) : Prop :=
  ∀ d ≤ β, MvPowerSeries.coeff d f = MvPowerSeries.coeff d g

namespace WindowEq

theorem refl (β : σ →₀ ℕ) (f : MvPowerSeries σ ℤ) : WindowEq β f f :=
  fun _ _ => rfl

theorem symm {β : σ →₀ ℕ} {f g : MvPowerSeries σ ℤ} (h : WindowEq β f g) :
    WindowEq β g f := fun d hd => (h d hd).symm

theorem trans {β : σ →₀ ℕ} {f g h : MvPowerSeries σ ℤ}
    (hfg : WindowEq β f g) (hgh : WindowEq β g h) : WindowEq β f h :=
  fun d hd => (hfg d hd).trans (hgh d hd)

theorem add {β : σ →₀ ℕ} {f f' g g' : MvPowerSeries σ ℤ}
    (hf : WindowEq β f f') (hg : WindowEq β g g') :
    WindowEq β (f + g) (f' + g') := by
  intro d hd
  simp only [map_add, hf d hd, hg d hd]

theorem mul {β : σ →₀ ℕ} {f f' g g' : MvPowerSeries σ ℤ}
    (hf : WindowEq β f f') (hg : WindowEq β g g') :
    WindowEq β (f * g) (f' * g') := by
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
    WindowEq β (MvPowerSeries.monomial d z * f) 0 := by
  intro e he
  rw [MvPowerSeries.coeff_monomial_mul, if_neg (fun hde => h (hde.trans he))]
  simp

end WindowEq

/-- Series invisible inside the coefficient window form an ideal. -/
def windowIdeal (β : σ →₀ ℕ) : Ideal (MvPowerSeries σ ℤ) where
  carrier := {f | WindowEq β f 0}
  zero_mem' := WindowEq.refl _ _
  add_mem' := by
    intro f g hf hg
    simpa using hf.add hg
  smul_mem' := by
    intro f g hg
    simpa using (WindowEq.refl β f).mul hg

theorem monomial_mem_windowIdeal (β d : σ →₀ ℕ) (z : ℤ) (h : ¬d ≤ β) :
    MvPowerSeries.monomial d z ∈ windowIdeal β := by
  have hh := WindowEq.monomial_mul_zero β d z 1 h
  simpa [windowIdeal] using hh

/-- Every combination of excluded generators remains invisible. -/
theorem span_monomials_le_windowIdeal (β : σ →₀ ℕ) (S : Set (σ →₀ ℕ))
    (h : ∀ d ∈ S, ¬d ≤ β) :
    Ideal.span ((fun d => MvPowerSeries.monomial d (1 : ℤ)) '' S) ≤ windowIdeal β := by
  apply Ideal.span_le.mpr
  rintro _ ⟨d, hd, rfl⟩
  exact monomial_mem_windowIdeal β d 1 (h d hd)

end
end Schubert.RS
