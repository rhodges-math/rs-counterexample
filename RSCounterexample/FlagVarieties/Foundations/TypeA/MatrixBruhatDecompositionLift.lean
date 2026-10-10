import RSCounterexample.FlagVarieties.Foundations.TypeA.MatrixBruhatDecompositionIndex

/-!
# Extending an upper-triangular matrix across one deleted index

The complementary indices retain their order under `Fin.succAbove`.
The extension acts by the given matrix on that complement, fixes the
inserted coordinate, and has zero cross blocks.
-/

namespace FlagVarieties.Foundations.TypeA

open Matrix

variable {n : ℕ} {K : Type*} [Field K]

/-- The matrix obtained from `U` by inserting a new row and column `p` that meet in the entry `1`
and are zero elsewhere. -/
noncomputable def liftUpperAt (p : Fin (n + 1))
    (U : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  (Matrix.fromBlocks U 0 0 (1 : Matrix Unit Unit K)).submatrix
    (insertIndexEquiv p).symm (insertIndexEquiv p).symm

@[simp] theorem liftUpperAt_complement (p : Fin (n + 1))
    (U : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    liftUpperAt p U (p.succAbove i) (p.succAbove j) = U i j := by
  simp only [← insertIndexEquiv_inl, liftUpperAt, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁]

@[simp] theorem liftUpperAt_pivot (p : Fin (n + 1))
    (U : Matrix (Fin n) (Fin n) K) :
    liftUpperAt p U p p = 1 := by
  have hp : (insertIndexEquiv p).symm p = .inr () := by
    simpa only [insertIndexEquiv_inr] using
      (insertIndexEquiv p).symm_apply_apply (Sum.inr ())
  simp only [liftUpperAt, Matrix.submatrix_apply, hp,
    Matrix.fromBlocks_apply₂₂]
  simp

@[simp] theorem liftUpperAt_complement_pivot (p : Fin (n + 1))
    (U : Matrix (Fin n) (Fin n) K) (i : Fin n) :
    liftUpperAt p U (p.succAbove i) p = 0 := by
  have hp : (insertIndexEquiv p).symm p = .inr () := by
    simpa only [insertIndexEquiv_inr] using
      (insertIndexEquiv p).symm_apply_apply (Sum.inr ())
  have hi : (insertIndexEquiv p).symm (p.succAbove i) = .inl i := by
    rw [← insertIndexEquiv_inl p i, Equiv.symm_apply_apply]
  simp only [liftUpperAt, Matrix.submatrix_apply, hp, hi,
    Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]

@[simp] theorem liftUpperAt_pivot_complement (p : Fin (n + 1))
    (U : Matrix (Fin n) (Fin n) K) (j : Fin n) :
    liftUpperAt p U p (p.succAbove j) = 0 := by
  have hp : (insertIndexEquiv p).symm p = .inr () := by
    simpa only [insertIndexEquiv_inr] using
      (insertIndexEquiv p).symm_apply_apply (Sum.inr ())
  have hj : (insertIndexEquiv p).symm (p.succAbove j) = .inl j := by
    rw [← insertIndexEquiv_inl p j, Equiv.symm_apply_apply]
  simp only [liftUpperAt, Matrix.submatrix_apply, hp, hj,
    Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]

theorem liftUpperAt_triangular (p : Fin (n + 1))
    (U : Matrix (Fin n) (Fin n) K) (hU : U.IsUpperTriangular) :
    (liftUpperAt p U).IsUpperTriangular := by
  intro i j hji
  obtain ⟨a, rfl⟩ := (insertIndexEquiv p).surjective i
  obtain ⟨b, rfl⟩ := (insertIndexEquiv p).surjective j
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          have hba : b < a := (Fin.strictMono_succAbove p).lt_iff_lt.mp hji
          simpa using hU hba
      | inr b =>
          cases b
          simp
  | inr a =>
      cases a
      cases b with
      | inl b => simp
      | inr b =>
          cases b
          exact (lt_irrefl p hji).elim

theorem liftUpperAt_det (p : Fin (n + 1))
    (U : Matrix (Fin n) (Fin n) K) :
    (liftUpperAt p U).det = U.det := by
  classical
  rw [liftUpperAt, Matrix.det_submatrix_equiv_self,
    Matrix.det_fromBlocks_zero₂₁]
  simp

theorem liftUpperAt_isUnit (p : Fin (n + 1))
    (U : Matrix (Fin n) (Fin n) K) (hU : IsUnit U) :
    IsUnit (liftUpperAt p U) := by
  classical
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [liftUpperAt_det]
  exact (Matrix.isUnit_iff_isUnit_det U).mp hU

end FlagVarieties.Foundations.TypeA
