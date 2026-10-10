import RSCounterexample.FlagVarieties.Foundations.TypeA.MatrixBruhatDecompositionBlockAssembly

/-!
# Type-A Bruhat decomposition by upper-triangular elimination

For every invertible square matrix over a field, this theorem constructs
upper-triangular invertible factors and the column-to-row
permutation matrix.  It proceeds by isolating a nonzero bottom pivot,
deleting its row and column, recursively factoring the invertible minor,
and re-inserting the pivot.
-/

namespace FlagVarieties.Foundations.TypeA

open Matrix

variable {K : Type*} [Field K]

theorem exists_upper_perm_upper_of_det_ne_zero :
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) K), A.det ≠ 0 →
      ∃ (B C : Matrix (Fin n) (Fin n) K) (w : Equiv.Perm (Fin n)),
        B.IsUpperTriangular ∧ C.IsUpperTriangular ∧
        IsUnit B ∧ IsUnit C ∧
        A = B * pivotMatrix (K := K) w * C := by
  intro n
  induction n with
  | zero =>
      intro A _
      refine ⟨1, 1, 1, Matrix.blockTriangular_one,
        Matrix.blockTriangular_one, isUnit_one, isUnit_one, ?_⟩
      ext i
      exact i.elim0
  | succ n ih =>
      intro A hdet
      obtain ⟨c, L, R, hL, hR, huL, huR, hp, hrow, hcol, hminor⟩ :=
        exists_isolated_bottom_pivot_with_invertible_minor A hdet
      let M := L * A * R
      let N := M.submatrix (Fin.last n).succAbove c.succAbove
      obtain ⟨U, V, w, hU, hV, huU, huV, hN⟩ := ih N hminor
      have hM : M = blockInsertAt (Fin.last n) c N (M (Fin.last n) c) :=
        isolated_eq_blockInsertAt M c hrow hcol
      rw [hN, blockInsertAt_factor] at hM
      let B' := blockInsertAt (Fin.last n) (Fin.last n) U (M (Fin.last n) c)
      let C' := blockInsertAt c c V 1
      have hB' : B'.IsUpperTriangular :=
        blockInsertAt_triangular (Fin.last n) U _ hU
      have hC' : C'.IsUpperTriangular :=
        blockInsertAt_triangular c V 1 hV
      have huB' : IsUnit B' :=
        blockInsertAt_isUnit (Fin.last n) U _ huU hp
      have huC' : IsUnit C' :=
        blockInsertAt_isUnit c V 1 huV one_ne_zero
      have hfactor : L * A * R =
          B' * pivotMatrix (K := K) (extendPermAt c w) * C' := by
        simpa only [M, B', C'] using hM
      have : Invertible L := huL.invertible
      have : Invertible R := huR.invertible
      have hLi : (L⁻¹).IsUpperTriangular :=
        Matrix.blockTriangular_inv_of_blockTriangular hL
      have hRi : (R⁻¹).IsUpperTriangular :=
        Matrix.blockTriangular_inv_of_blockTriangular hR
      have huLi : IsUnit (L⁻¹) :=
        (Matrix.isUnit_iff_isUnit_det _).mpr
          (Matrix.isUnit_nonsing_inv_det L ((Matrix.isUnit_iff_isUnit_det L).mp huL))
      have huRi : IsUnit (R⁻¹) :=
        (Matrix.isUnit_iff_isUnit_det _).mpr
          (Matrix.isUnit_nonsing_inv_det R ((Matrix.isUnit_iff_isUnit_det R).mp huR))
      refine ⟨L⁻¹ * B', C' * R⁻¹, extendPermAt c w,
        hLi.mul hB', hC'.mul hRi,
        huLi.mul huB', huC'.mul huRi, ?_⟩
      calc
        A = L⁻¹ * (L * A * R) * R⁻¹ := by
          simp [Matrix.mul_assoc]
        _ = (L⁻¹ * B') * pivotMatrix (K := K) (extendPermAt c w) *
            (C' * R⁻¹) := by rw [hfactor]; simp [Matrix.mul_assoc]

theorem exists_upper_perm_upper_of_isUnit {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (hA : IsUnit A) :
    ∃ (B C : Matrix (Fin n) (Fin n) K) (w : Equiv.Perm (Fin n)),
      B.IsUpperTriangular ∧ C.IsUpperTriangular ∧
      IsUnit B ∧ IsUnit C ∧
      A = B * pivotMatrix (K := K) w * C :=
  exists_upper_perm_upper_of_det_ne_zero n A
    ((Matrix.isUnit_iff_isUnit_det A).mp hA).ne_zero

end FlagVarieties.Foundations.TypeA
