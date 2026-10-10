import RSCounterexample.LinearProgramming.Matrix.Bareiss
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Rat.Star

/-!
# Gram matrices of independent rows

The Gram matrix `R Rᵀ` of an integer matrix `R` with linearly independent rows is positive
definite (`Matrix.PosDef.mul_conjTranspose_self`), and so are its leading principal submatrices.
Hence its leading principal minors are positive (`LinearProgramming.gram_leadMinor_pos`). In
particular fraction-free elimination of a Gram matrix needs no pivoting.

## Main definitions

* `LinearProgramming.gram R N`: the Gram matrix `(∑_{j < N} R a j * R b j)_{a, b}` of the rows
  of `R`.
* `LinearProgramming.RowsIndep R m N`: the first `m` rows of `R`, of length `N`, are linearly
  independent over `ℚ`.

## Main results

* `LinearProgramming.gram_posDef`: the Gram matrix of independent rows is positive definite.
* `LinearProgramming.gram_leadMinor_pos`: its leading principal minors are positive.
-/

namespace LinearProgramming

open Matrix

/-- The Gram matrix of the rows of `R`, of length `N`. -/
def gram (R : ℕ → ℕ → ℤ) (N : ℕ) (a b : ℕ) : ℤ := ∑ j : Fin N, R a j * R b j

/-- The first `m` rows of `R`, of length `N`, are linearly independent over `ℚ`. -/
def RowsIndep (R : ℕ → ℕ → ℤ) (m N : ℕ) : Prop :=
  ∀ x : Fin m → ℚ, (∀ j : Fin N, ∑ a : Fin m, x a * R a j = 0) → x = 0

/-- The first `m` rows of `R` as a rational matrix. -/
def rowsQ (R : ℕ → ℕ → ℤ) (m N : ℕ) : Matrix (Fin m) (Fin N) ℚ := Matrix.of fun a j => R a j

/-- **Positive-definiteness of the Gram matrix** of independent rows. -/
theorem gram_posDef {R : ℕ → ℕ → ℤ} {m N : ℕ} (h : RowsIndep R m N) :
    (rowsQ R m N * (rowsQ R m N)ᵀ).PosDef := by
  have hinj : Function.Injective (rowsQ R m N).vecMul := by
    intro x y hxy
    have hxy' : x ᵥ* rowsQ R m N = y ᵥ* rowsQ R m N := hxy
    have h0 : (x - y) ᵥ* rowsQ R m N = 0 := by rw [sub_vecMul, hxy', sub_self]
    have := h (x - y) fun j => by
      have := congrFun h0 j
      simpa [vecMul, dotProduct, rowsQ] using this
    exact sub_eq_zero.mp this
  have := PosDef.mul_conjTranspose_self (rowsQ R m N) hinj
  rwa [conjTranspose_eq_transpose_of_trivial] at this

/-- **The leading principal minors of the Gram matrix of independent rows are positive.** -/
theorem gram_leadMinor_pos {R : ℕ → ℕ → ℤ} {m N : ℕ} (h : RowsIndep R m N) {l : ℕ}
    (hl : l ≤ m) : 0 < leadMinor (gram R N) l := by
  have hpd := (gram_posDef h).submatrix (Fin.castLE_injective hl)
  have hdet := hpd.det_pos
  have heq : ((leadMinor (gram R N) l : ℤ) : ℚ) =
      ((rowsQ R m N * (rowsQ R m N)ᵀ).submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
    rw [leadMinor_intCast]
    unfold leadMinor
    congr 1
    ext a b
    simp [gram, rowsQ, mul_apply]
  rw [← heq] at hdet
  exact_mod_cast hdet

end LinearProgramming
