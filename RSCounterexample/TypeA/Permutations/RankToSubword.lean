import RSCounterexample.TypeA.Permutations.RankSortingWord

/-!
# Rank inequalities give a reduced adjacent sorting subword

Induction removes the first letter of an arbitrary reduced
sorting word of the upper permutation. The rank-matrix lifting theorems
choose whether the lower permutation takes that descent or skips it.
The result is a sublist, not an abstract order witness.
-/

namespace Schubert.FinPermutation

variable {n : ℕ}

theorem reduced_sorting_subword_of_strongBruhatLE
    (u v : FinPermutation n) (word : List (AdjacentPosition n))
    (hprod : applyRightAdjacentWord word v = Equiv.refl (Fin n))
    (hlen : word.length = v.length) (huv : u ≤ᴮ v) :
    ∃ sub : List (AdjacentPosition n),
      sub.Sublist word ∧
      applyRightAdjacentWord sub u = Equiv.refl (Fin n) ∧
      sub.length = u.length := by
  induction word generalizing u v with
  | nil =>
      have hv : v = Equiv.refl (Fin n) := by simpa using hprod
      subst v
      have hu : u = Equiv.refl (Fin n) :=
        strongBruhat_antisymm huv (refl_strongBruhatLE u)
      subst u
      exact ⟨[], List.Sublist.refl [], rfl, by simp⟩
  | cons a tail ih =>
      obtain ⟨hv, htail, htaillen⟩ :=
        reduced_sorting_cons_data v a tail hprod hlen
      rcases descent_or_ascent u a with hu | hu
      · have hle := rightAdjacentSwap_strongBruhatLE_of_both_descent
          a huv hu hv
        obtain ⟨sub, hsub, hsort, hsublen⟩ :=
          ih (u.rightAdjacentSwap a) (v.rightAdjacentSwap a)
            htail htaillen hle
        refine ⟨a :: sub, hsub.cons_cons a, hsort, ?_⟩
        have hdrop := length_rightAdjacentSwap_of_descent u a hu
        simp only [List.length_cons]
        omega
      · have hle := strongBruhatLE_rightAdjacentSwap_of_ascent_descent
          a huv hu hv
        obtain ⟨sub, hsub, hsort, hsublen⟩ :=
          ih u (v.rightAdjacentSwap a) htail htaillen hle
        exact ⟨sub, hsub.cons a, hsort, hsublen⟩

end Schubert.FinPermutation
