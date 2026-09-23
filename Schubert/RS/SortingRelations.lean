import Schubert.RS.Sorting
import Schubert.RS.OperatorRelations

/-! Local sorting diamonds used to remove dependence on the selected ascent. -/

namespace Schubert.RS

open FinPermutation Schubert
variable {n : ℕ}

theorem firstAscent_minimal (a : Composition n) (h : (ascentSet a).Nonempty)
    (i : AdjacentPosition n) (hi : a i.left < a i.right) :
    (firstAscent a h).left.val ≤ i.left.val := by
  let k : Fin (n - 1) := ⟨i.left.val, by have := i.hasRight; omega⟩
  have hk : adjacentPosition k = i := by apply AdjacentPosition.ext; rfl
  have hm : k ∈ ascentSet a := by simp [ascentSet, hk, hi]
  exact Finset.min'_le (ascentSet a) k hm

theorem swapComposition_commute (a : Composition n) (i j : AdjacentPosition n)
    (h : SeparatedAdjacentPositions i j) :
    swapComposition (swapComposition a i) j =
      swapComposition (swapComposition a j) i := by
  funext k
  exact congrArg a (congrFun (adjacentTransposition_commute_of_separated i j h) k)

theorem swapComposition_braid (a : Composition n) (i j : AdjacentPosition n)
    (h : i.right = j.left) :
    swapComposition (swapComposition (swapComposition a i) j) i =
      swapComposition (swapComposition (swapComposition a j) i) j := by
  funext k
  exact congrArg a (congrFun (adjacentTransposition_braid i j h) k)

theorem ascent_after_separated_swap (a : Composition n) (i j : AdjacentPosition n)
    (h : SeparatedAdjacentPositions i j) (hj : a j.left < a j.right) :
    swapComposition a i j.left < swapComposition a i j.right := by
  obtain ⟨hll, hlr, hrl, hrr⟩ := separated_endpoint_ne i j h
  simpa [swapComposition_other _ _ _ hll.symm hrl.symm,
    swapComposition_other _ _ _ hlr.symm hrr.symm] using hj

/-- All four interior edges of the adjacent sorting diamond are strict ascents. -/
theorem adjacent_sorting_diamond (a : Composition n) (i j : AdjacentPosition n)
    (h : i.right = j.left) (hi : a i.left < a i.right) (hj : a j.left < a j.right) :
    (swapComposition a i j.left < swapComposition a i j.right) ∧
    (swapComposition (swapComposition a i) j i.left <
      swapComposition (swapComposition a i) j i.right) ∧
    (swapComposition a j i.left < swapComposition a j i.right) ∧
    (swapComposition (swapComposition a j) i j.left <
      swapComposition (swapComposition a j) i j.right) := by
  have hxy : i.left ≠ j.left := by rw [← h]; exact i.left_ne_right
  have hxz : i.left ≠ j.right := (i.left_lt_right.trans (h ▸ j.left_lt_right)).ne
  have hzy : j.right ≠ i.right := by rw [h]; exact j.left_ne_right.symm
  have hij : a i.left < a j.right := hi.trans (h ▸ hj)
  simp only [swapComposition, adjacentTransposition, h, Equiv.swap_apply_left,
    Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hxy hxz,
    Equiv.swap_apply_of_ne_of_ne hxz.symm j.left_ne_right.symm]
  exact ⟨hij, hj, hij, h ▸ hi⟩

end Schubert.RS
