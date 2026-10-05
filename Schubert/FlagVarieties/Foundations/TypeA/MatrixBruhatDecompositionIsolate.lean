import Schubert.FlagVarieties.Foundations.TypeA.MatrixBruhatDecompositionLeftClear

/-!
# Isolating the bottom pivot by upper Borel operations

For an invertible matrix, the bottom row and the chosen pivot column can
be reduced to a single common nonzero entry.  This is the inductive
Bruhat elimination step before deleting that row and column.
-/

namespace FlagVarieties.Foundations.TypeA

open Matrix

variable {n : ℕ} {K : Type*} [Field K]

theorem exists_isolated_bottom_pivot
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (hdet : A.det ≠ 0) :
    ∃ (c : Fin (n + 1))
      (L R : Matrix (Fin (n + 1)) (Fin (n + 1)) K),
      L.IsUpperTriangular ∧ R.IsUpperTriangular ∧
      IsUnit L ∧ IsUnit R ∧
      (L * A * R) (Fin.last n) c ≠ 0 ∧
      (∀ j : Fin (n + 1), j ≠ c → (L * A * R) (Fin.last n) j = 0) ∧
      ∀ i : Fin (n + 1), i ≠ Fin.last n → (L * A * R) i c = 0 := by
  classical
  obtain ⟨c, hp, hleft⟩ := invertible_bottom_row_leftmost_pivot A hdet
  obtain ⟨R, hR, huR, hRp, hRzero⟩ :=
    exists_upper_right_clear A (Fin.last n) c hp hleft
  let A' := A * R
  have hp' : A' (Fin.last n) c ≠ 0 := by simpa [A', hRp] using hp
  let S : Finset (Fin (n + 1)) :=
    Finset.univ.filter (fun i => i < Fin.last n)
  have hS : ∀ i ∈ S, i < Fin.last n := by
    intro i hi
    simpa [S] using hi
  obtain ⟨L, hL, huL, _, hLzero, hLkeep⟩ :=
    exists_upper_left_clear_finset A' (Fin.last n) c hp' S hS
  have hlast : Fin.last n ∉ S := by simp [S]
  refine ⟨c, L, R, hL, hR, huL, huR, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc]
    rw [hLkeep (Fin.last n) hlast c]
    exact hp'
  · intro j hj
    rw [Matrix.mul_assoc]
    rw [hLkeep (Fin.last n) hlast j]
    exact hRzero j hj
  · intro i hi
    have hilast : i < Fin.last n := lt_of_le_of_ne (Fin.le_last i) hi
    have hiS : i ∈ S := by simp [S, hilast]
    rw [Matrix.mul_assoc]
    exact hLzero i hiS

end FlagVarieties.Foundations.TypeA
