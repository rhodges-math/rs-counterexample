import Schubert.TypeA.Permutations.RankLiftingAscent

/-!
# Reduced adjacent words and their sorting orientation

`applyRightAdjacentWord word w` applies the displayed letters in list
order as right position swaps. Thus a reduced sorting word for `w`
starts at `w` and ends at identity; reversing it gives a reduced word
whose product from identity is `w`.
-/

namespace Schubert.FinPermutation

variable {n : ℕ}

theorem reduced_sorting_cons_data
    (v : FinPermutation n) (a : AdjacentPosition n)
    (tail : List (AdjacentPosition n))
    (hprod : applyRightAdjacentWord (a :: tail) v =
      Equiv.refl (Fin n))
    (hlen : (a :: tail).length = v.length) :
    v.HasDescent a.left ∧
      applyRightAdjacentWord tail (v.rightAdjacentSwap a) =
        Equiv.refl (Fin n) ∧
      tail.length = (v.rightAdjacentSwap a).length := by
  have hdesc : IsDescendingWord v (a :: tail) := by
    apply isDescendingWord_of_length_eq
    rw [hprod, length_refl]
    simpa using hlen
  have hv : v.HasDescent a.left := hdesc.1
  refine ⟨hv, hprod, ?_⟩
  have hdrop := length_rightAdjacentSwap_of_descent v a hv
  simp only [List.length_cons] at hlen
  omega

theorem reduced_product_iff_reduced_sorting_reverse
    (w : FinPermutation n) (word : List (AdjacentPosition n)) :
    (applyRightAdjacentWord word (Equiv.refl (Fin n)) = w ∧
      word.length = w.length) ↔
    (applyRightAdjacentWord word.reverse w = Equiv.refl (Fin n) ∧
      word.reverse.length = w.length) := by
  constructor
  · rintro ⟨hprod, hlen⟩
    constructor
    · rw [applyRightAdjacentWord_eq_trans,
        applyRightAdjacentWord_reverse_refl, hprod]
      ext p
      simp
    · simpa using hlen
  · rintro ⟨hsort, hlen⟩
    have hinv := applyRightAdjacentWord_refl_eq_symm_of_eq_refl hsort
    rw [applyRightAdjacentWord_reverse_refl] at hinv
    constructor
    · simpa using congrArg Equiv.symm hinv
    · simpa using hlen

theorem canonical_reduced_sorting_word (w : FinPermutation n) :
    applyRightAdjacentWord (reducedWordToRefl w) w =
        Equiv.refl (Fin n) ∧
      (reducedWordToRefl w).length = w.length :=
  ⟨apply_reducedWordToRefl w, length_reducedWordToRefl w⟩

end Schubert.FinPermutation
