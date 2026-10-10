import RSCounterexample.FlagVarieties.Foundations.TypeA.MatrixBruhatDecompositionIsolate

/-!
# Invertibility of the complementary minor

Once the bottom pivot column is isolated, Laplace expansion along that
column proves that deleting the bottom row and pivot column
leaves an invertible smaller matrix.
-/

namespace FlagVarieties.Foundations.TypeA

open Matrix

variable {n : ℕ} {K : Type*} [Field K]

theorem det_eq_bottom_pivot_mul_minor
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (c : Fin (n + 1))
    (hcol : ∀ i : Fin (n + 1), i ≠ Fin.last n → M i c = 0) :
    M.det = (-1 : K) ^ ((Fin.last n : Fin (n + 1)).val + c.val) *
      M (Fin.last n) c *
      (M.submatrix (Fin.last n).succAbove c.succAbove).det := by
  classical
  rw [Matrix.det_succ_column M c]
  rw [Finset.sum_eq_single (Fin.last n)]
  · intro i _ hi
    rw [hcol i hi]
    ring
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem isolated_bottom_minor_det_ne_zero
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hdet : M.det ≠ 0) (c : Fin (n + 1))
    (hcol : ∀ i : Fin (n + 1), i ≠ Fin.last n → M i c = 0) :
    (M.submatrix (Fin.last n).succAbove c.succAbove).det ≠ 0 := by
  intro hz
  apply hdet
  rw [det_eq_bottom_pivot_mul_minor M c hcol, hz, mul_zero]

/-- The isolated matrix from `exists_isolated_bottom_pivot` has an
invertible complementary minor of size `n`. -/
theorem exists_isolated_bottom_pivot_with_invertible_minor
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (hdet : A.det ≠ 0) :
    ∃ (c : Fin (n + 1))
      (L R : Matrix (Fin (n + 1)) (Fin (n + 1)) K),
      L.IsUpperTriangular ∧ R.IsUpperTriangular ∧
      IsUnit L ∧ IsUnit R ∧
      (L * A * R) (Fin.last n) c ≠ 0 ∧
      (∀ j : Fin (n + 1), j ≠ c → (L * A * R) (Fin.last n) j = 0) ∧
      (∀ i : Fin (n + 1), i ≠ Fin.last n → (L * A * R) i c = 0) ∧
      ((L * A * R).submatrix (Fin.last n).succAbove c.succAbove).det ≠ 0 := by
  classical
  obtain ⟨c, L, R, hL, hR, huL, huR, hp, hrow, hcol⟩ :=
    exists_isolated_bottom_pivot A hdet
  have hLdet : L.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det L).mp huL).ne_zero
  have hRdet : R.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det R).mp huR).ne_zero
  have hMdet : (L * A * R).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_mul]
    exact mul_ne_zero (mul_ne_zero hLdet hdet) hRdet
  exact ⟨c, L, R, hL, hR, huL, huR, hp, hrow, hcol,
    isolated_bottom_minor_det_ne_zero (L * A * R) hMdet c hcol⟩

end FlagVarieties.Foundations.TypeA
