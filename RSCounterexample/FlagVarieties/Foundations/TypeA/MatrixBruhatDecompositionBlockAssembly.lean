import RSCounterexample.FlagVarieties.Foundations.TypeA.MatrixBruhatDecompositionBlockInsert

/-!
# Reassembling the isolated pivot and an inductive factorization

The block equalities use the old permutation matrix and concrete
matrix multiplication.  They supply the algebraic induction step; no
rank or orbit predicate is used to define the factors.
-/

namespace FlagVarieties.Foundations.TypeA

open Matrix

variable {n : ℕ} {K : Type*} [Field K]

theorem isolated_eq_blockInsertAt
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (c : Fin (n + 1))
    (hrow : ∀ j : Fin (n + 1), j ≠ c → M (Fin.last n) j = 0)
    (hcol : ∀ i : Fin (n + 1), i ≠ Fin.last n → M i c = 0) :
    M = blockInsertAt (Fin.last n) c
      (M.submatrix (Fin.last n).succAbove c.succAbove)
      (M (Fin.last n) c) := by
  classical
  ext i j
  obtain ⟨a, rfl⟩ := (insertIndexEquiv (Fin.last n)).surjective i
  obtain ⟨b, rfl⟩ := (insertIndexEquiv c).surjective j
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          simpa only [insertIndexEquiv_inl, Fin.succAbove_last,
            Matrix.submatrix_apply] using
            (blockInsertAt_complement (Fin.last n) c
              (M.submatrix (Fin.last n).succAbove c.succAbove)
              (M (Fin.last n) c) a b).symm
      | inr b =>
          cases b
          have hz : M a.castSucc c = 0 := hcol _ (Fin.castSucc_ne_last a)
          simpa only [insertIndexEquiv_inl, insertIndexEquiv_inr,
            Fin.succAbove_last] using
            hz.trans (blockInsertAt_row_pivot (Fin.last n) c
              (M.submatrix (Fin.last n).succAbove c.succAbove)
              (M (Fin.last n) c) a).symm
  | inr a =>
      cases a
      cases b with
      | inl b => simp [hrow _ (Fin.succAbove_ne _ _)]
      | inr b => cases b; simp

theorem blockInsertAt_factor
    (c : Fin (n + 1))
    (U V : Matrix (Fin n) (Fin n) K)
    (w : Equiv.Perm (Fin n)) (d : K) :
    blockInsertAt (Fin.last n) c (U * pivotMatrix (K := K) w * V) d =
      blockInsertAt (Fin.last n) (Fin.last n) U d *
        pivotMatrix (K := K) (extendPermAt c w) *
        blockInsertAt c c V 1 := by
  classical
  let er := insertIndexEquiv (Fin.last n)
  let ec := insertIndexEquiv c
  let BU : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) K :=
    Matrix.fromBlocks U 0 0 (Matrix.of fun (_ _ : Unit) => d)
  let BP : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) K :=
    Matrix.fromBlocks (pivotMatrix (K := K) w) 0 0 (1 : Matrix Unit Unit K)
  let BV : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) K :=
    Matrix.fromBlocks V 0 0 (1 : Matrix Unit Unit K)
  have hP : pivotMatrix (K := K) (extendPermAt c w) =
      BP.submatrix er.symm ec.symm := by
    ext i j
    have hh := congrArg
      (fun X : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) K =>
        X (er.symm i) (ec.symm j))
      (pivotMatrix_extendPermAt_blocks (K := K) c w)
    simpa [BP, er, ec, Matrix.submatrix_apply] using hh
  have hmul : BU.submatrix er.symm er.symm *
      BP.submatrix er.symm ec.symm * BV.submatrix ec.symm ec.symm =
      (BU * BP * BV).submatrix er.symm ec.symm := by
    rw [Matrix.submatrix_mul_equiv BU BP er.symm er.symm ec.symm,
      Matrix.submatrix_mul_equiv (BU * BP) BV er.symm ec.symm ec.symm]
  have hblock : BU * BP * BV =
      Matrix.fromBlocks (U * pivotMatrix (K := K) w * V) 0 0
        (Matrix.of fun (_ _ : Unit) => d) := by
    simp [BU, BP, BV, Matrix.fromBlocks_multiply]
  change (Matrix.fromBlocks (U * pivotMatrix (K := K) w * V) 0 0
    (Matrix.of fun (_ _ : Unit) => d)).submatrix er.symm ec.symm =
      BU.submatrix er.symm er.symm *
        pivotMatrix (K := K) (extendPermAt c w) *
        BV.submatrix ec.symm ec.symm
  rw [hP, hmul, hblock]

end FlagVarieties.Foundations.TypeA
