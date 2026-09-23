import Schubert.TypeA.Permutations.BruhatGraded
import Schubert.RS.Support.BruhatRanks
import Schubert.TypeA.Permutations.LongestBruhatDuality

namespace Schubert.RS.Representation
open FinPermutation

/-- The second half of the mixed right lifting property. -/
theorem right_reflected_lower_le_upper {n : ℕ} (i : AdjacentPosition n)
    {u v : FinPermutation n} (h : u ≤ᴮ v)
    (hu : u i.left < u i.right) (hv : v i.right < v i.left) :
    u.rightAdjacentSwap i ≤ᴮ v := by
  have hr : v.trans (Fin.revPerm : FinPermutation n) ≤ᴮ
      u.trans (Fin.revPerm : FinPermutation n) :=
    (strongBruhatLE_trans_revPerm_iff v u).mpr h
  have hva : (v.trans (Fin.revPerm : FinPermutation n)) i.left <
      (v.trans (Fin.revPerm : FinPermutation n)) i.right := by
    exact Fin.rev_lt_rev.mpr hv
  have hud : HasDescent (u.trans (Fin.revPerm : FinPermutation n)) i.left := by
    apply (hasDescent_left_iff _ i).mpr
    exact Fin.rev_lt_rev.mpr hu
  have hs := strongBruhatLE_rightAdjacentSwap_of_ascent_descent i hr hva hud
  change v.trans (Fin.revPerm : FinPermutation n) ≤ᴮ
    (u.rightAdjacentSwap i).trans (Fin.revPerm : FinPermutation n) at hs
  exact (strongBruhatLE_trans_revPerm_iff _ _).mp hs

theorem left_lower_le_reflected_upper {n : ℕ} (i : AdjacentPosition n)
    {u v : FinPermutation n} (h : u ≤ᴮ v)
    (hu : u.symm i.left < u.symm i.right) (hv : v.symm i.right < v.symm i.left) :
    u ≤ᴮ v.leftAdjacentSwap i := by
  apply (strongBruhatLE_symm_iff _ _).mp
  exact strongBruhatLE_rightAdjacentSwap_of_ascent_descent i
    ((strongBruhatLE_symm_iff u v).mpr h) hu ((hasDescent_left_iff _ i).mpr hv)

theorem left_reflected_lower_le_upper {n : ℕ} (i : AdjacentPosition n)
    {u v : FinPermutation n} (h : u ≤ᴮ v)
    (hu : u.symm i.left < u.symm i.right) (hv : v.symm i.right < v.symm i.left) :
    u.leftAdjacentSwap i ≤ᴮ v := by
  apply (strongBruhatLE_symm_iff _ _).mp
  exact right_reflected_lower_le_upper i ((strongBruhatLE_symm_iff u v).mpr h) hu hv

theorem left_reflection_le_of_descent {n : ℕ} (i : AdjacentPosition n)
    (w : FinPermutation n) (h : w.symm i.right < w.symm i.left) :
    w.leftAdjacentSwap i ≤ᴮ w :=
  leftAdjacentSwap_le_of_inverseDescent w i ((hasDescent_left_iff _ i).mpr h)

theorem left_reflections_le_of_both_descent {n : ℕ} (i : AdjacentPosition n)
    {u v : FinPermutation n} (h : u ≤ᴮ v)
    (hu : u.symm i.right < u.symm i.left) (hv : v.symm i.right < v.symm i.left) :
    u.leftAdjacentSwap i ≤ᴮ v.leftAdjacentSwap i := by
  apply (strongBruhatLE_symm_iff _ _).mp
  exact rightAdjacentSwap_strongBruhatLE_of_both_descent i
    ((strongBruhatLE_symm_iff u v).mpr h)
    ((hasDescent_left_iff _ i).mpr hu) ((hasDescent_left_iff _ i).mpr hv)

theorem le_left_reflection_of_ascent {n : ℕ} (i : AdjacentPosition n)
    (w : FinPermutation n) (h : w.symm i.left < w.symm i.right) :
    w ≤ᴮ w.leftAdjacentSwap i := by
  have hd : (w.leftAdjacentSwap i).symm i.right < (w.leftAdjacentSwap i).symm i.left := by
    simpa only [leftAdjacentSwap,adjacentTransposition,Equiv.symm_trans,Equiv.symm_swap,
      Equiv.trans_apply,Equiv.swap_apply_left,Equiv.swap_apply_right] using h
  have he : (w.leftAdjacentSwap i).leftAdjacentSwap i = w := by
    apply Equiv.ext
    intro j
    simp [leftAdjacentSwap,adjacentTransposition]
  simpa only [he] using left_reflection_le_of_descent i (w.leftAdjacentSwap i) hd

end Schubert.RS.Representation
