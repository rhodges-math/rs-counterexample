import Schubert.FlagVarieties.Foundations.TypeA.MatrixBruhatDecompositionPivot

/-!
# The first bottom-row pivot of an invertible matrix

Choosing the leftmost nonzero entry is compatible with right
upper-triangular elimination: columns to its left are already zero,
and the permitted transvections clear columns to its right.
-/

namespace FlagVarieties.Foundations.TypeA

open Matrix

variable {n : ℕ} {K : Type*} [Field K]

theorem invertible_bottom_row_has_nonzero
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (hdet : A.det ≠ 0) :
    ∃ c : Fin (n + 1), A (Fin.last n) c ≠ 0 := by
  classical
  by_contra h
  push Not at h
  exact hdet (Matrix.det_eq_zero_of_row_eq_zero (Fin.last n) h)

/-- The leftmost bottom-row pivot is nonzero and all preceding entries
vanish.  No rank-based pivot definition is involved. -/
theorem invertible_bottom_row_leftmost_pivot
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (hdet : A.det ≠ 0) :
    ∃ c : Fin (n + 1),
      A (Fin.last n) c ≠ 0 ∧
      ∀ j : Fin (n + 1), j < c → A (Fin.last n) j = 0 := by
  classical
  let s : Finset (Fin (n + 1)) :=
    Finset.univ.filter (fun c => A (Fin.last n) c ≠ 0)
  obtain ⟨c, hc⟩ := invertible_bottom_row_has_nonzero A hdet
  have hs : s.Nonempty := ⟨c, by simp [s, hc]⟩
  refine ⟨s.min' hs, ?_, ?_⟩
  · have hmem := Finset.min'_mem s hs
    simpa [s] using hmem
  · intro j hj
    by_contra hne
    have hmem : j ∈ s := by simp [s, hne]
    exact (not_le_of_gt hj) (Finset.min'_le s j hmem)

end FlagVarieties.Foundations.TypeA
