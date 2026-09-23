import Schubert.RS.Representation.Torus
import Schubert.RS.Laurent
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators

/-- The integer character of the full diagonal torus. -/
def integerWeightScalar {n : ℕ} (w : Weight n) (t : DiagonalTorus n) : ℂ :=
  ∏ i, (t i : ℂ) ^ w i

theorem integerWeightScalar_ne_zero {n : ℕ} (w : Weight n) (t : DiagonalTorus n) :
    integerWeightScalar w t ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => zpow_ne_zero _ (Units.ne_zero (t i)))

theorem integerWeightScalar_nat {n : ℕ} (u : Fin n → ℕ) (t : DiagonalTorus n) :
    integerWeightScalar (fun i => (u i : ℤ)) t = weightScalar u t := by
  simp [integerWeightScalar, weightScalar]

theorem integerWeightScalar_add {n : ℕ} (v w : Weight n) (t : DiagonalTorus n) :
    integerWeightScalar (v+w) t = integerWeightScalar v t * integerWeightScalar w t := by
  simp only [integerWeightScalar, Pi.add_apply, zpow_add₀ (Units.ne_zero _), Finset.prod_mul_distrib]

theorem integerWeightScalar_mul {n : ℕ} (w : Weight n) (s t : DiagonalTorus n) :
    integerWeightScalar w (s*t) = integerWeightScalar w s * integerWeightScalar w t := by
  simp [integerWeightScalar, mul_zpow, Finset.prod_mul_distrib]

def coordinateTorus {n : ℕ} (i : Fin n) : DiagonalTorus n :=
  fun j => if j = i then Units.mk0 (2 : ℂ) (by norm_num) else 1

theorem integerWeightScalar_coordinate {n : ℕ} (w : Weight n) (i : Fin n) :
    integerWeightScalar w (coordinateTorus i) = (2 : ℂ)^w i := by
  classical
  simp [integerWeightScalar, coordinateTorus, apply_ite]

theorem integerWeightScalar_injective {n : ℕ} :
    Function.Injective (integerWeightScalar (n := n)) := by
  intro v w h
  funext i
  have hi := congrFun h (coordinateTorus i)
  rw [integerWeightScalar_coordinate, integerWeightScalar_coordinate] at hi
  have hr : (2 : ℝ)^v i = 2^w i := by
    apply Complex.ofReal_injective
    simpa using hi
  exact zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hr

/-- The simultaneous eigenspace for an integral character of the full
diagonal torus. -/
def torusWeightSpace {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : DiagonalTorus n →* Module.End ℂ E) (w : Weight n) : Submodule ℂ E where
  carrier := {x | ∀ t, ρ t x = integerWeightScalar w t • x}
  zero_mem' := by intro t; simp
  add_mem' := by intro x y hx hy t; simp only [map_add, hx t, hy t, smul_add]
  smul_mem' := by intro c x hx t; simp only [map_smul, hx t, smul_comm c]

/-- Torus-equivariant isomorphisms restrict to isomorphisms of weight spaces. -/
def torusWeightSpaceEquiv {n : ℕ} {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F]
    (ρ : DiagonalTorus n →* Module.End ℂ E) (σ : DiagonalTorus n →* Module.End ℂ F)
    (e : E ≃ₗ[ℂ] F) (he : ∀ t x, e (ρ t x) = σ t (e x)) (w : Weight n) :
    torusWeightSpace ρ w ≃ₗ[ℂ] torusWeightSpace σ w where
  toFun x := ⟨e x.val, by intro t; rw [← he, x.property t, map_smul]⟩
  invFun y := ⟨e.symm y.val, by
    intro t
    apply e.injective
    rw [he, e.apply_symm_apply, y.property t, map_smul, e.apply_symm_apply]⟩
  left_inv x := by ext; exact e.symm_apply_apply x.val
  right_inv y := by ext; exact e.apply_symm_apply y.val
  map_add' x y := Subtype.ext (e.map_add x.val y.val)
  map_smul' c x := Subtype.ext (e.map_smul c x.val)

theorem torusWeightSpace_finrank_eq {n : ℕ} {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F]
    (ρ : DiagonalTorus n →* Module.End ℂ E) (σ : DiagonalTorus n →* Module.End ℂ F)
    (e : E ≃ₗ[ℂ] F) (he : ∀ t x, e (ρ t x) = σ t (e x)) (w : Weight n) :
    Module.finrank ℂ (torusWeightSpace ρ w) = Module.finrank ℂ (torusWeightSpace σ w) :=
  (torusWeightSpaceEquiv ρ σ e he w).finrank_eq

end
end Schubert.RS.Representation
