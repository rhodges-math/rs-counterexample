import Schubert.LinearProgramming.Chubanov.Perceptron

/-!
# Rescaling columns by powers of two

The projection-and-rescaling algorithm keeps an exponent `k j` for every column and works with
the integer matrix `M̃ = M diag(2^(R - k j))` (`LinearProgramming.scaled`), whose kernel is
`diag(2^(k j)) ker M` as long as every `k j ≤ R`. Positive column scaling keeps the rows
independent (`LinearProgramming.RowsIndep.scaled`). Kernel vectors move back and forth between
`M` and `M̃` (`LinearProgramming.mulVec_scaled_up`, `LinearProgramming.mulVec_scaled_down`).

## Main definitions

* `LinearProgramming.scaled M R k`: the matrix `M diag(2^(R - k j))`.
* `LinearProgramming.KerBox m N M x`: `x` is in the kernel of `M` and in the unit cube.

## Main results

* `LinearProgramming.RowsIndep.scaled`: scaling keeps independent rows independent.
* `LinearProgramming.mulVec_scaled_up`: `x ∈ ker M` gives `diag(2^k) x ∈ ker M̃`.
* `LinearProgramming.mulVec_scaled_down`: `y ∈ ker M̃` gives `diag(2^(R - k)) y ∈ ker M`.
-/

namespace LinearProgramming

open Matrix

/-- The matrix `M diag(2^(R - k j))`: column `j` of `M` scaled by `2^(R - k j)`. -/
def scaled (M : ℕ → ℕ → ℤ) (R : ℕ) (k : ℕ → ℕ) (i j : ℕ) : ℤ := M i j * 2 ^ (R - k j)

/-- `x` is in the kernel of the `m × N` matrix `M` and in the unit cube `[0, 1]ᴺ`. -/
def KerBox (m N : ℕ) (M : ℕ → ℕ → ℤ) (x : Fin N → ℚ) : Prop :=
  rowsQ M m N *ᵥ x = 0 ∧ ∀ j, 0 ≤ x j ∧ x j ≤ 1

variable {m N : ℕ} {M : ℕ → ℕ → ℤ}

theorem rowsQ_mulVec_apply (A : ℕ → ℕ → ℤ) (x : Fin N → ℚ) (i : Fin m) :
    (rowsQ A m N *ᵥ x) i = ∑ j : Fin N, (A i j : ℚ) * x j := rfl

/-- Positive column scaling keeps the rows independent. -/
theorem RowsIndep.scaled (h : RowsIndep M m N) (R : ℕ) (k : ℕ → ℕ) :
    RowsIndep (scaled M R k) m N := by
  intro x hx
  apply h x
  intro j
  have := hx j
  simp only [LinearProgramming.scaled, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at this
  have hpow : (0 : ℚ) < 2 ^ (R - k j) := by positivity
  have h2 : (∑ a : Fin m, x a * M a j) * 2 ^ (R - k j) = 0 := by
    rw [Finset.sum_mul, ← this]
    exact Finset.sum_congr rfl fun a _ => by ring
  exact (mul_eq_zero.mp h2).resolve_right hpow.ne'

/-- **Kernel vectors of `M` scale up into the kernel of `M̃`**: `x ↦ diag(2^k) x`. -/
theorem mulVec_scaled_up {R : ℕ} {k : ℕ → ℕ} (hk : ∀ j : Fin N, k j ≤ R) {x : Fin N → ℚ}
    (hx : rowsQ M m N *ᵥ x = 0) :
    rowsQ (scaled M R k) m N *ᵥ (fun j => 2 ^ k j * x j) = 0 := by
  funext i
  have h := congrFun hx i
  rw [rowsQ_mulVec_apply] at h ⊢
  simp only [LinearProgramming.scaled, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Pi.zero_apply]
  have : ∀ j : Fin N,
      (M i j : ℚ) * 2 ^ (R - k j) * (2 ^ k j * x j) = 2 ^ R * ((M i j : ℚ) * x j) := fun j => by
      rw [show (2 : ℚ) ^ R = 2 ^ (R - k j) * 2 ^ k j by
        rw [← pow_add, Nat.sub_add_cancel (hk j)]]
      ring
  rw [Finset.sum_congr rfl fun j _ => this j, ← Finset.mul_sum, h, Pi.zero_apply, mul_zero]

/-- **Kernel vectors of `M̃` scale down into the kernel of `M`**: `y ↦ diag(2^(R - k)) y`. -/
theorem mulVec_scaled_down {R : ℕ} {k : ℕ → ℕ} {y : Fin N → ℚ}
    (hy : rowsQ (scaled M R k) m N *ᵥ y = 0) :
    rowsQ M m N *ᵥ (fun j => 2 ^ (R - k j) * y j) = 0 := by
  funext i
  have h := congrFun hy i
  rw [rowsQ_mulVec_apply] at h ⊢
  simp only [LinearProgramming.scaled, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    Pi.zero_apply] at h ⊢
  rw [← h]
  exact Finset.sum_congr rfl fun j _ => by ring

end LinearProgramming
