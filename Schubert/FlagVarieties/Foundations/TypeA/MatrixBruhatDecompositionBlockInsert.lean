import Schubert.FlagVarieties.Foundations.TypeA.MatrixBruhatDecompositionPermutation

/-!
# Inserting a scalar pivot beside a smaller matrix

This is a reindexed block matrix: the smaller matrix occupies
the complement of the specified row and column, with zero cross blocks
and scalar at their intersection.
-/

namespace FlagVarieties.Foundations.TypeA

open Matrix

variable {n : ℕ} {K : Type*} [Field K]

/-- The matrix obtained from `N` by inserting a new row `r` and column `c` that meet in the entry
`d` and are zero elsewhere. -/
noncomputable def blockInsertAt (r c : Fin (n + 1))
    (N : Matrix (Fin n) (Fin n) K) (d : K) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  (Matrix.fromBlocks N 0 0 (Matrix.of fun (_ _ : Unit) => d)).submatrix
    (insertIndexEquiv r).symm (insertIndexEquiv c).symm

@[simp] theorem blockInsertAt_complement (r c : Fin (n + 1))
    (N : Matrix (Fin n) (Fin n) K) (d : K) (i j : Fin n) :
    blockInsertAt r c N d (r.succAbove i) (c.succAbove j) = N i j := by
  simp [blockInsertAt]

@[simp] theorem blockInsertAt_row_pivot (r c : Fin (n + 1))
    (N : Matrix (Fin n) (Fin n) K) (d : K) (i : Fin n) :
    blockInsertAt r c N d (r.succAbove i) c = 0 := by
  simp [blockInsertAt]

@[simp] theorem blockInsertAt_column_pivot (r c : Fin (n + 1))
    (N : Matrix (Fin n) (Fin n) K) (d : K) (j : Fin n) :
    blockInsertAt r c N d r (c.succAbove j) = 0 := by
  simp [blockInsertAt]

@[simp] theorem blockInsertAt_pivot (r c : Fin (n + 1))
    (N : Matrix (Fin n) (Fin n) K) (d : K) :
    blockInsertAt r c N d r c = d := by
  simp [blockInsertAt]

theorem blockInsertAt_triangular (p : Fin (n + 1))
    (U : Matrix (Fin n) (Fin n) K) (d : K)
    (hU : U.IsUpperTriangular) :
    (blockInsertAt p p U d).IsUpperTriangular := by
  intro i j hji
  obtain ⟨a, rfl⟩ := (insertIndexEquiv p).surjective i
  obtain ⟨b, rfl⟩ := (insertIndexEquiv p).surjective j
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          have hba : b < a := (Fin.strictMono_succAbove p).lt_iff_lt.mp hji
          simpa using hU hba
      | inr b => cases b; simp
  | inr a =>
      cases a
      cases b with
      | inl b => simp
      | inr b => cases b; exact (lt_irrefl p hji).elim

theorem blockInsertAt_det (p : Fin (n + 1))
    (U : Matrix (Fin n) (Fin n) K) (d : K) :
    (blockInsertAt p p U d).det = U.det * d := by
  classical
  rw [blockInsertAt, Matrix.det_submatrix_equiv_self,
    Matrix.det_fromBlocks_zero₂₁]
  simp

theorem blockInsertAt_isUnit (p : Fin (n + 1))
    (U : Matrix (Fin n) (Fin n) K) (d : K)
    (hU : IsUnit U) (hd : d ≠ 0) :
    IsUnit (blockInsertAt p p U d) := by
  classical
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply IsUnit.mk0
  rw [blockInsertAt_det]
  exact mul_ne_zero ((Matrix.isUnit_iff_isUnit_det U).mp hU).ne_zero hd

end FlagVarieties.Foundations.TypeA
