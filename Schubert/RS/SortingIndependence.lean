import Schubert.RS.SortingRelations

/-!
# Independence of the chosen adjacent ascent

The proof follows terminating sorting diamonds. It uses exactly the braid and
commutation relations already proved for the key and atom operators.
-/

namespace Schubert.RS

open FinPermutation Schubert
noncomputable section
variable {n : ℕ}

theorem recursion_at_every_ascent {V : Type*}
    (op : AdjacentPosition n → V → V) (F : Composition n → V)
    (comm : ∀ i j, SeparatedAdjacentPositions i j → ∀ v, op i (op j v) = op j (op i v))
    (braid : ∀ i j, i.right = j.left → ∀ v,
      op i (op j (op i v)) = op j (op i (op j v)))
    (step : ∀ a (h : (ascentSet a).Nonempty),
      F a = op (firstAscent a h) (F (swapComposition a (firstAscent a h)))) :
    ∀ a i, a i.left < a i.right → F a = op i (F (swapComposition a i)) := by
  intro a
  induction a using (measure sortingMeasure).wf.induction with
  | h a ih =>
    intro i hi
    have ha : (ascentSet a).Nonempty := by
      by_contra hh
      exact (not_lt_of_ge (antitone_of_no_ascent a hh i.left_lt_right.le)) hi
    let j := firstAscent a ha
    have hj : a j.left < a j.right := firstAscent_lt a ha
    have hmin : j.left.val ≤ i.left.val := firstAscent_minimal a ha i hi
    have hjlt := sortingMeasure_swap_lt a j hj
    have hilt := sortingMeasure_swap_lt a i hi
    by_cases heq : j = i
    · simpa only [← heq] using step a ha
    have hstrict : j.left.val < i.left.val := by
      have hne : j.left ≠ i.left := fun he => heq (AdjacentPosition.ext he)
      have hv : j.left.val ≠ i.left.val := fun he => hne (Fin.ext he)
      omega
    by_cases hadj : j.right = i.left
    · obtain ⟨hji, hjij, hij, hiji⟩ := adjacent_sorting_diamond a j i hadj hj hi
      have hjilt := (sortingMeasure_swap_lt (swapComposition a j) i hji).trans hjlt
      have hijlt := (sortingMeasure_swap_lt (swapComposition a i) j hij).trans hilt
      calc
        F a = op j (F (swapComposition a j)) := step a ha
        _ = op j (op i (F (swapComposition (swapComposition a j) i))) := by
          rw [ih _ hjlt i hji]
        _ = op j (op i (op j (F (swapComposition (swapComposition (swapComposition a j) i) j)))) := by
          rw [ih _ hjilt j hjij]
        _ = op i (op j (op i (F (swapComposition (swapComposition (swapComposition a j) i) j)))) :=
          braid j i hadj _
        _ = op i (op j (op i (F (swapComposition (swapComposition (swapComposition a i) j) i)))) := by
          rw [swapComposition_braid a j i hadj]
        _ = op i (op j (F (swapComposition (swapComposition a i) j))) := by
          rw [← ih _ hijlt i hiji]
        _ = op i (F (swapComposition a i)) := by rw [← ih _ hilt j hij]
    · have hsep : SeparatedAdjacentPositions j i := by
        left
        have hn : j.right.val ≠ i.left.val := fun he => hadj (Fin.ext he)
        have hr := j.right_val
        change j.right.val < i.left.val
        omega
      have hji := ascent_after_separated_swap a j i hsep hi
      have hij := ascent_after_separated_swap a i j (hsep.elim Or.inr Or.inl) hj
      calc
        F a = op j (F (swapComposition a j)) := step a ha
        _ = op j (op i (F (swapComposition (swapComposition a j) i))) := by
          rw [ih _ hjlt i hji]
        _ = op i (op j (F (swapComposition (swapComposition a j) i))) := comm j i hsep _
        _ = op i (op j (F (swapComposition (swapComposition a i) j))) := by
          rw [swapComposition_commute a j i hsep]
        _ = op i (F (swapComposition a i)) := by rw [← ih _ hilt j hij]

/-- The key definition obeys the manuscript's recursion at every strict ascent. -/
theorem key_any_ascent (a : Composition n) (i : AdjacentPosition n)
    (hi : a i.left < a i.right) :
    key a = isobaric i (key (swapComposition a i)) :=
  recursion_at_every_ascent isobaric key isobaric_commute isobaric_braid key_ascent a i hi

/-- The atom definition obeys the same sorting convention at every strict ascent. -/
theorem atom_any_ascent (a : Composition n) (i : AdjacentPosition n)
    (hi : a i.left < a i.right) :
    atom a = atomOperator i (atom (swapComposition a i)) :=
  recursion_at_every_ascent atomOperator atom atomOperator_commute atomOperator_braid atom_ascent a i hi

end
end Schubert.RS
