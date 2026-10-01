import Schubert.LinearProgramming.Matrix.Gram
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The orthogonal projection onto a kernel, with integer entries

Let `A` be an integer `m × N` matrix with linearly independent rows, `G = A Aᵀ` its Gram matrix,
and `P = I - Aᵀ G⁻¹ A` the orthogonal projection of `ℚᴺ` onto the kernel of `A`. The projection
is symmetric and idempotent, it kills the rows of `A`, it fixes the kernel of `A`, and its
diagonal entries lie in `[0, 1]` (`LinearProgramming.proj_symm`, `LinearProgramming.proj_idem`,
`LinearProgramming.mul_proj`, `LinearProgramming.proj_mulVec_of_mulVec_eq_zero`,
`LinearProgramming.proj_diag_le_one`).

Its multiple `δ P`, with `δ = det G`, is an integer matrix computed by one fraction-free
elimination. Run `m` steps of Bareiss elimination on the `(m + N) × (m + N)` matrix
`[[G, A], [Aᵀ, I]]` (`LinearProgramming.projBlock`): no pivot vanishes, since they are Gram
determinants of independent rows. The last pivot is `δ`, and the trailing `N × N` block is `δ P`
(`LinearProgramming.bareiss_projBlock`). Each trailing entry is a bordered minor
`det [[G, A e_b], [e_aᵀ Aᵀ, [a = b]]]`, which the Schur complement formula evaluates to
`det G · P a b`.

## Main definitions

* `LinearProgramming.projQ A m N`: the projection `P` over `ℚ`.
* `LinearProgramming.projBlock A m N`: the matrix `[[A Aᵀ, A], [Aᵀ, I]]`.

## Main results

* `LinearProgramming.bareiss_projBlock`: fraction-free elimination computes `det G` and `δ P`.
-/

namespace LinearProgramming

open Matrix

variable (A : ℕ → ℕ → ℤ) (m N : ℕ)

/-- The Gram matrix `A Aᵀ` over `ℚ`. -/
def gramQ : Matrix (Fin m) (Fin m) ℚ := rowsQ A m N * (rowsQ A m N)ᵀ

/-- The orthogonal projection `I - Aᵀ (A Aᵀ)⁻¹ A` onto the kernel of `A`. -/
noncomputable def projQ : Matrix (Fin N) (Fin N) ℚ :=
  1 - (rowsQ A m N)ᵀ * (gramQ A m N)⁻¹ * rowsQ A m N

variable {A m N}

theorem gramQ_det_ne_zero (h : RowsIndep A m N) : (gramQ A m N).det ≠ 0 :=
  (gram_posDef h).det_pos.ne'

theorem gramQ_transpose : (gramQ A m N)ᵀ = gramQ A m N := by
  simp [gramQ, transpose_mul]

/-- The projection is symmetric. -/
theorem proj_symm : (projQ A m N)ᵀ = projQ A m N := by
  simp only [projQ, transpose_sub, transpose_one, transpose_mul, transpose_transpose,
    transpose_nonsing_inv, gramQ_transpose, Matrix.mul_assoc]

/-- The projection kills the rows: `A P = 0`. -/
theorem mul_proj (h : RowsIndep A m N) : rowsQ A m N * projQ A m N = 0 := by
  have hu : IsUnit (gramQ A m N).det := isUnit_iff_ne_zero.mpr (gramQ_det_ne_zero h)
  rw [projQ, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    show rowsQ A m N * (rowsQ A m N)ᵀ = gramQ A m N from rfl, mul_nonsing_inv _ hu,
    Matrix.one_mul, sub_self]

/-- The projection is idempotent. -/
theorem proj_idem (h : RowsIndep A m N) : projQ A m N * projQ A m N = projQ A m N := by
  have hXP : (rowsQ A m N)ᵀ * (gramQ A m N)⁻¹ * rowsQ A m N * projQ A m N = 0 := by
    rw [Matrix.mul_assoc, mul_proj h, Matrix.mul_zero]
  nth_rewrite 1 [projQ]
  rw [Matrix.sub_mul, Matrix.one_mul, hXP, sub_zero]

/-- The projection fixes the kernel of `A`. -/
theorem proj_mulVec_of_mulVec_eq_zero {x : Fin N → ℚ} (hx : rowsQ A m N *ᵥ x = 0) :
    projQ A m N *ᵥ x = x := by
  rw [projQ, sub_mulVec, one_mulVec, ← mulVec_mulVec, hx, mulVec_zero, sub_zero]

/-- The projection maps into the kernel of `A`. -/
theorem mulVec_proj_mulVec (h : RowsIndep A m N) (y : Fin N → ℚ) :
    rowsQ A m N *ᵥ (projQ A m N *ᵥ y) = 0 := by
  rw [mulVec_mulVec, mul_proj h, zero_mulVec]

/-- `v · P w = P v · w`, by symmetry. -/
theorem dotProduct_proj_comm (v w : Fin N → ℚ) :
    v ⬝ᵥ (projQ A m N *ᵥ w) = (projQ A m N *ᵥ v) ⬝ᵥ w := by
  rw [dotProduct_mulVec, ← mulVec_transpose, proj_symm]

/-- `P v · P v = v · P v`, by symmetry and idempotence. -/
theorem proj_dot_self (h : RowsIndep A m N) (v : Fin N → ℚ) :
    (projQ A m N *ᵥ v) ⬝ᵥ (projQ A m N *ᵥ v) = v ⬝ᵥ (projQ A m N *ᵥ v) := by
  rw [← dotProduct_proj_comm, mulVec_mulVec, proj_idem h]

/-- A symmetric idempotent matrix has nonnegative diagonal entries: `S k k = ∑ i, S i k ^ 2`. -/
theorem diag_nonneg_of_symm_idem {S : Matrix (Fin N) (Fin N) ℚ} (hs : Sᵀ = S) (hi : S * S = S)
    (k : Fin N) : 0 ≤ S k k := by
  rw [← hi, mul_apply]
  refine Finset.sum_nonneg fun i _ => ?_
  have : S k i = S i k := by rw [← transpose_apply S i k, hs]
  rw [this]
  exact mul_self_nonneg _

/-- The diagonal entries of the projection are nonnegative. -/
theorem proj_diag_nonneg (h : RowsIndep A m N) (k : Fin N) : 0 ≤ projQ A m N k k :=
  diag_nonneg_of_symm_idem proj_symm (proj_idem h) k

/-- The diagonal entries of the projection are at most `1`: the complementary projection
`I - P` is also symmetric and idempotent. -/
theorem proj_diag_le_one (h : RowsIndep A m N) (k : Fin N) : projQ A m N k k ≤ 1 := by
  have hs : (1 - projQ A m N)ᵀ = 1 - projQ A m N := by
    rw [transpose_sub, transpose_one, proj_symm]
  have hi : (1 - projQ A m N) * (1 - projQ A m N) = 1 - projQ A m N := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, proj_idem h, sub_self, sub_zero]
  have := diag_nonneg_of_symm_idem hs hi k
  rw [Matrix.sub_apply, one_apply_eq] at this
  linarith

/-! ### The integer projection by fraction-free elimination -/

/-- The `(m + N) × (m + N)` matrix `[[A Aᵀ, A], [Aᵀ, I]]`. -/
def projBlock (A : ℕ → ℕ → ℤ) (m N : ℕ) (a b : ℕ) : ℤ :=
  if a < m then (if b < m then gram A N a b else A a (b - m))
  else (if b < m then A b (a - m) else if a = b then 1 else 0)

theorem leadMinor_projBlock {l : ℕ} (hl : l ≤ m) :
    leadMinor (projBlock A m N) l = leadMinor (gram A N) l := by
  unfold leadMinor
  congr 1
  ext a b
  simp [projBlock, show (a : ℕ) < m by omega, show (b : ℕ) < m by omega]

theorem leadMinor_gram_eq_det : ((leadMinor (gram A N) m : ℤ) : ℚ) = (gramQ A m N).det := by
  rw [leadMinor_intCast]
  unfold leadMinor
  congr 1
  ext a b
  simp [gram, gramQ, rowsQ, mul_apply]

/-- **The trailing bordered minors of `[[G, A], [Aᵀ, I]]`** are `det G · P`, by the Schur
complement formula. -/
theorem borderedMinor_projBlock (h : RowsIndep A m N) (a b : Fin N) :
    ((borderedMinor (projBlock A m N) m (m + a) (m + b) : ℤ) : ℚ) =
      (gramQ A m N).det * projQ A m N a b := by
  classical
  have : Invertible (gramQ A m N) :=
    invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr (gramQ_det_ne_zero h))
  rw [borderedMinor_intCast, borderedMinor,
    ← det_submatrix_equiv_self (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1))]
  have hblocks : (Matrix.of fun c d : Fin (m + 1) =>
      ((projBlock A m N (bord m (m + a) c) (bord m (m + b) d) : ℤ) : ℚ)).submatrix
        finSumFinEquiv finSumFinEquiv =
      fromBlocks (gramQ A m N) (Matrix.of fun i _ => (A i b : ℚ))
        (Matrix.of fun _ i => (A i a : ℚ)) (Matrix.of fun _ _ => if a = b then 1 else 0) := by
    ext (i | i) (j | j)
    · simp [bord, projBlock, gramQ, rowsQ, gram, mul_apply]
    · simp [bord, projBlock]
    · simp [bord, projBlock]
    · have h1 : ¬ (m + (a : ℕ) < m) := by omega
      have h2 : ¬ (m + (b : ℕ) < m) := by omega
      simp [bord, projBlock, h1, h2, Fin.ext_iff]
  rw [hblocks, det_fromBlocks₁₁, invOf_eq_nonsing_inv, det_fin_one]
  congr 1

/-- **Fraction-free elimination computes the projection.** For `A` with independent rows, `m`
steps of Bareiss elimination on `[[A Aᵀ, A], [Aᵀ, I]]` end with the pivot `δ = det (A Aᵀ) > 0`,
and the trailing block is `δ P`. -/
theorem bareiss_projBlock (h : RowsIndep A m N) :
    0 < (bareiss (projBlock A m N) m).2 ∧
      ((bareiss (projBlock A m N) m).2 : ℚ) = (gramQ A m N).det ∧
      ∀ a b : Fin N, ((bareiss (projBlock A m N) m).1 (m + a) (m + b) : ℚ) =
        (gramQ A m N).det * projQ A m N a b := by
  obtain ⟨h1, h2⟩ := bareiss_int_eq_borderedMinor (projBlock A m N) m fun l hl hlm => by
    rw [leadMinor_projBlock hlm.le]
    exact (gram_leadMinor_pos h hlm.le).ne'
  rw [leadMinor_projBlock le_rfl] at h2
  refine ⟨h2 ▸ gram_leadMinor_pos h le_rfl, by rw [h2, leadMinor_gram_eq_det], fun a b => ?_⟩
  rw [h1 _ _ (by omega) (by omega), borderedMinor_projBlock h]

end LinearProgramming
