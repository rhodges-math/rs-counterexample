import RSCounterexample.FlagVarieties.Foundations.TypeA.MatrixBruhatDecompositionLift
import RSCounterexample.FlagVarieties.Foundations.TypeA.PivotMatrix

/-!
# Inserting the bottom pivot into a permutation matrix

The existing `pivotMatrix` convention sends a column `j` to its pivot
row `w j`.  The extended permutation sends the new pivot column `c` to
the bottom row and preserves the order of all other row/column labels.
-/

namespace FlagVarieties.Foundations.TypeA

open Matrix

variable {n : ℕ} {K : Type*} [Field K]

/-- The permutation of `Fin (n + 1)` sending `c` to the last index and acting as `w` on the
remaining indices (both listed in order). -/
noncomputable def extendPermAt (c : Fin (n + 1))
    (w : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  (insertIndexEquiv c).symm.trans
    ((w.sumCongr (Equiv.refl Unit)).trans (insertIndexEquiv (Fin.last n)))

@[simp] theorem extendPermAt_pivot (c : Fin (n + 1))
    (w : Equiv.Perm (Fin n)) :
    extendPermAt c w c = Fin.last n := by
  have hc : (insertIndexEquiv c).symm c = .inr () := by
    simpa only [insertIndexEquiv_inr] using
      (insertIndexEquiv c).symm_apply_apply (Sum.inr ())
  simp [extendPermAt, hc]

@[simp] theorem extendPermAt_complement (c : Fin (n + 1))
    (w : Equiv.Perm (Fin n)) (j : Fin n) :
    extendPermAt c w (c.succAbove j) = (Fin.last n).succAbove (w j) := by
  have hj : (insertIndexEquiv c).symm (c.succAbove j) = .inl j := by
    simpa only [insertIndexEquiv_inl] using
      (insertIndexEquiv c).symm_apply_apply (Sum.inl j)
  simp [extendPermAt, hj]

/-- The pivot matrix of the extended permutation is a block
insertion of the old pivot matrix and a single unit pivot. -/
theorem pivotMatrix_extendPermAt_blocks (c : Fin (n + 1))
    (w : Equiv.Perm (Fin n)) :
    (pivotMatrix (K := K) (extendPermAt c w)).submatrix
      (insertIndexEquiv (Fin.last n)) (insertIndexEquiv c) =
      Matrix.fromBlocks (pivotMatrix (K := K) w) 0 0
        (1 : Matrix Unit Unit K) := by
  classical
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          simp [pivotMatrix]
      | inr j =>
          cases j
          have hne : Fin.last n ≠ i.castSucc := (Fin.castSucc_ne_last i).symm
          simp [pivotMatrix, hne]
  | inr i =>
      cases i
      cases j with
      | inl j => simp [pivotMatrix]
      | inr j => cases j; simp [pivotMatrix]

end FlagVarieties.Foundations.TypeA
