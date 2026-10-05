import Schubert.TypeA.Permutations.RankToSubword

/-!
# A reduced adjacent sorting subword gives rank inequalities

The upper sorting word is arbitrary. A skipped first letter compares
the lower permutation to the upper adjacent descent. A retained first
letter gives two smaller sorting words; the simultaneous-ascent lifting
theorem restores their first letters.
-/

namespace Schubert.FinPermutation

variable {n : ℕ}

theorem strongBruhatLE_of_reduced_sorting_subword
    (u v : FinPermutation n)
    (word sub : List (AdjacentPosition n))
    (hprod : applyRightAdjacentWord word v = Equiv.refl (Fin n))
    (hlen : word.length = v.length)
    (hsub : sub.Sublist word)
    (hsubprod : applyRightAdjacentWord sub u = Equiv.refl (Fin n))
    (hsublen : sub.length = u.length) : u ≤ᴮ v := by
  induction word generalizing u v sub with
  | nil =>
      have hv : v = Equiv.refl (Fin n) := by simpa using hprod
      have hsubnil : sub = [] := by
        cases sub with
        | nil => rfl
        | cons a tail =>
            have hlenSub := hsub.length_le
            simp at hlenSub
      subst sub
      have hu : u = Equiv.refl (Fin n) := by simpa using hsubprod
      subst u
      subst v
      exact strongBruhat_refl _
  | cons a tail ih =>
      obtain ⟨hv, htail, htaillen⟩ :=
        reduced_sorting_cons_data v a tail hprod hlen
      cases sub with
      | nil =>
          have hu : u = Equiv.refl (Fin n) := by simpa using hsubprod
          subst u
          exact refl_strongBruhatLE v
      | cons b rest =>
          rcases List.cons_sublist_cons'.mp hsub with hskip | ⟨hba, htake⟩
          · have hle := ih u (v.rightAdjacentSwap a) (b :: rest)
              htail htaillen hskip hsubprod hsublen
            exact strongBruhat_trans hle
              (rightAdjacentSwap_le_of_descent v a hv)
          · subst b
            obtain ⟨hu, hsubtail, hsublentail⟩ :=
              reduced_sorting_cons_data u a rest hsubprod hsublen
            have hle := ih (u.rightAdjacentSwap a)
              (v.rightAdjacentSwap a) rest htail htaillen
              htake hsubtail hsublentail
            have hua : (u.rightAdjacentSwap a) a.left <
                (u.rightAdjacentSwap a) a.right := by
              simpa [rightAdjacentSwap_apply_left,
                rightAdjacentSwap_apply_right] using
                (hasDescent_left_iff u a).mp hu
            have hva : (v.rightAdjacentSwap a) a.left <
                (v.rightAdjacentSwap a) a.right := by
              simpa [rightAdjacentSwap_apply_left,
                rightAdjacentSwap_apply_right] using
                (hasDescent_left_iff v a).mp hv
            have hswap := rightAdjacentSwap_strongBruhatLE_of_both_ascent
              a hle hua hva
            simpa only [rightAdjacentSwap_involutive] using hswap

end Schubert.FinPermutation
