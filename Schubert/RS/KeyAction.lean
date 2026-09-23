import Schubert.RS.SortingIndependence

/-! The complete 0-Hecke action on keys, including equal adjacent entries. -/

namespace Schubert.RS

open FinPermutation Schubert
noncomputable section
variable {n : ℕ}

theorem compositionMonomial_symmetric (a : Composition n) (i : AdjacentPosition n)
    (h : a i.left = a i.right) :
    adjacentVariableSwap i (compositionMonomial a) = compositionMonomial a := by
  rw [compositionMonomial, adjacentVariableSwap_monomial]
  apply congrArg (fun d : Fin n →₀ ℕ => MvPolynomial.monomial d (1 : ℤ))
  ext k
  by_cases hl : k = i.left
  · subst k
    simpa using h.symm
  · by_cases hr : k = i.right
    · subst k
      simpa using h
    · exact replaceAdjacentExponents_of_ne _ _ _ _ _ hl hr

theorem key_isobaric_of_equal (a : Composition n) (i : AdjacentPosition n)
    (heq : a i.left = a i.right) : isobaric i (key a) = key a := by
  induction a using (measure sortingMeasure).wf.induction generalizing i with
  | h a ih =>
    by_cases ha : (ascentSet a).Nonempty
    · let j := firstAscent a ha
      have hj : a j.left < a j.right := firstAscent_lt a ha
      have hjlt := sortingMeasure_swap_lt a j hj
      have hji : j ≠ i := by rintro rfl; omega
      by_cases hadj : i.right = j.left
      · have hxz : i.left ≠ j.right :=
          (i.left_lt_right.trans (hadj ▸ j.left_lt_right)).ne
        have hxy : i.left ≠ j.left := by rw [← hadj]; exact i.left_ne_right
        have hzy : j.right ≠ i.right := by rw [hadj]; exact j.left_ne_right.symm
        have h1 : (swapComposition a j) i.left < (swapComposition a j) i.right := by
          simpa [swapComposition, adjacentTransposition, ← hadj,
            Equiv.swap_apply_def, i.left_ne_right, hxz, heq] using hj
        have h2 : (swapComposition (swapComposition a j) i) j.left =
            (swapComposition (swapComposition a j) i) j.right := by
          simp [swapComposition, adjacentTransposition, ← hadj,
            Equiv.swap_apply_def, i.left_ne_right, i.left_ne_right.symm,
            hxz, hxz.symm, hzy, heq]
        have h2lt := (sortingMeasure_swap_lt (swapComposition a j) i h1).trans hjlt
        rw [key_ascent a ha, key_any_ascent _ i h1]
        rw [isobaric_braid i j hadj]
        rw [ih _ h2lt j h2]
      · by_cases hadj' : j.right = i.left
        · have hxz : j.left ≠ i.right :=
            (j.left_lt_right.trans (hadj' ▸ i.left_lt_right)).ne
          have hzy : i.right ≠ j.right := by rw [hadj']; exact i.left_ne_right.symm
          have hxy : j.left ≠ i.left := by rw [← hadj']; exact j.left_ne_right
          have h1 : (swapComposition a j) i.left < (swapComposition a j) i.right := by
            simpa [swapComposition, adjacentTransposition, ← hadj',
              Equiv.swap_apply_of_ne_of_ne hxz.symm hzy, ← heq] using hj
          have h2 : (swapComposition (swapComposition a j) i) j.left =
              (swapComposition (swapComposition a j) i) j.right := by
            simp [swapComposition, adjacentTransposition, hadj',
              Equiv.swap_apply_def, hxy, hxy.symm, hxz, hxz.symm,
              i.left_ne_right, i.left_ne_right.symm, heq]
          have h2lt := (sortingMeasure_swap_lt (swapComposition a j) i h1).trans hjlt
          rw [key_ascent a ha, key_any_ascent _ i h1]
          rw [← isobaric_braid j i hadj']
          rw [ih _ h2lt j h2]
        · have hs : SeparatedAdjacentPositions i j := by
            have hn : i.left.val ≠ j.left.val := by
              intro h
              exact hji (AdjacentPosition.ext (Fin.ext h).symm)
            have hn1 : i.right.val ≠ j.left.val := fun h => hadj (Fin.ext h)
            have hn2 : j.right.val ≠ i.left.val := fun h => hadj' (Fin.ext h)
            have hi := i.right_val
            have hjr := j.right_val
            change i.right.val < j.left.val ∨ j.right.val < i.left.val
            omega
          obtain ⟨hll, hlr, hrl, hrr⟩ := separated_endpoint_ne i j hs
          have hi' : (swapComposition a j) i.left = (swapComposition a j) i.right := by
            simpa [swapComposition_other _ _ _ hll hlr,
              swapComposition_other _ _ _ hrl hrr] using heq
          rw [key_ascent a ha, isobaric_commute i j hs, ih _ hjlt i hi']
    · rw [key_of_no_ascent a ha]
      exact isobaric_of_symmetric i _ (compositionMonomial_symmetric a i heq)

theorem isobaric_key (a : Composition n) (i : AdjacentPosition n) :
    isobaric i (key a) =
      if a i.right < a i.left then key (swapComposition a i) else key a := by
  split_ifs with h
  · have hs : (swapComposition a i) i.left < (swapComposition a i) i.right := by
      simpa using h
    rw [key_any_ascent _ i hs, swapComposition_involutive]
  · by_cases he : a i.left = a i.right
    · exact key_isobaric_of_equal a i he
    · have hl : a i.left < a i.right := by omega
      rw [key_any_ascent a i hl, isobaric_idempotent]

end
end Schubert.RS
