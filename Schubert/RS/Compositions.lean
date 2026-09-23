import Schubert.TypeA.Permutations.AdjacentTranspositions

/-!
# Terminating adjacent sorting of weak compositions

Sorting an adjacent strict ascent decreases the natural-number weighted sum
`sum i, i * a i`. No bounded-fuel fallback occurs in the definitions of keys.
-/

namespace Schubert.RS

open FinPermutation

abbrev Composition (n : ℕ) := Fin n → ℕ

variable {n : ℕ}

def swapComposition (a : Composition n) (i : AdjacentPosition n) : Composition n :=
  fun j => a (adjacentTransposition i j)

@[simp] theorem swapComposition_left (a : Composition n) (i : AdjacentPosition n) :
    swapComposition a i i.left = a i.right := by
  simp [swapComposition, adjacentTransposition]

@[simp] theorem swapComposition_right (a : Composition n) (i : AdjacentPosition n) :
    swapComposition a i i.right = a i.left := by
  simp [swapComposition, adjacentTransposition]

theorem swapComposition_other (a : Composition n) (i : AdjacentPosition n)
    (j : Fin n) (hl : j ≠ i.left) (hr : j ≠ i.right) :
    swapComposition a i j = a j := by
  simp [swapComposition, adjacentTransposition, Equiv.swap_apply_of_ne_of_ne hl hr]

@[simp] theorem swapComposition_involutive (a : Composition n) (i : AdjacentPosition n) :
    swapComposition (swapComposition a i) i = a := by
  funext j
  simp [swapComposition, adjacentTransposition]

def sortingMeasure (a : Composition n) : ℕ := ∑ j, j.val * a j

theorem sortingMeasure_swap (a : Composition n) (i : AdjacentPosition n) :
    sortingMeasure (swapComposition a i) + a i.right =
      sortingMeasure a + a i.left := by
  classical
  let s := (Finset.univ.erase i.left).erase i.right
  have hr : i.right ∈ (Finset.univ.erase i.left : Finset (Fin n)) := by
    simp [i.left_ne_right.symm]
  have split (f : Fin n → ℕ) :
      (∑ j ∈ s, f j) + f i.right + f i.left = ∑ j, f j := by
    rw [Finset.sum_erase_add _ _ hr, Finset.sum_erase_add _ _ (Finset.mem_univ _)]
  have heq : (∑ j ∈ s, j.val * swapComposition a i j) = ∑ j ∈ s, j.val * a j := by
    apply Finset.sum_congr rfl
    intro j hj
    have h := Finset.mem_erase.mp hj
    have h' := Finset.mem_erase.mp h.2
    rw [swapComposition_other a i j h'.1 h.1]
  have h₁ := split (fun j => j.val * a j)
  have h₂ := split (fun j => j.val * swapComposition a i j)
  rw [heq, swapComposition_left, swapComposition_right, AdjacentPosition.right_val] at h₂
  rw [AdjacentPosition.right_val] at h₁
  unfold sortingMeasure
  simp only [Nat.add_mul, Nat.one_mul] at h₁ h₂
  omega

theorem sortingMeasure_swap_lt (a : Composition n) (i : AdjacentPosition n)
    (h : a i.left < a i.right) :
    sortingMeasure (swapComposition a i) < sortingMeasure a := by
  have := sortingMeasure_swap a i
  omega

/-- Index adjacent positions without excluding ranks zero and one. -/
def adjacentPosition (j : Fin (n - 1)) : AdjacentPosition n where
  left := ⟨j.val, by omega⟩
  hasRight := by change j.val + 1 < n; omega

def ascentSet (a : Composition n) : Finset (Fin (n - 1)) :=
  Finset.univ.filter fun j => a (adjacentPosition j).left < a (adjacentPosition j).right

def firstAscent (a : Composition n) (h : (ascentSet a).Nonempty) : AdjacentPosition n :=
  adjacentPosition ((ascentSet a).min' h)

theorem firstAscent_lt (a : Composition n) (h : (ascentSet a).Nonempty) :
    a (firstAscent a h).left < a (firstAscent a h).right := by
  have hm := Finset.min'_mem (ascentSet a) h
  exact (Finset.mem_filter.mp hm).2

theorem sortingMeasure_firstAscent (a : Composition n) (h : (ascentSet a).Nonempty) :
    sortingMeasure (swapComposition a (firstAscent a h)) < sortingMeasure a :=
  sortingMeasure_swap_lt a _ (firstAscent_lt a h)

end Schubert.RS
