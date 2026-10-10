import RSCounterexample.TypeA.Permutations.BruhatGraded
import RSCounterexample.TypeA.Permutations.NorthwestRankBounds
import RSCounterexample.TypeA.Permutations.LongestBruhatDuality
import RSCounterexample.TypeA.Permutations.AdjacentLength

/-!
# Simultaneous adjacent ascents preserve rank-matrix Bruhat order

Postcomposition by the longest permutation complements all values and
reverses Bruhat order. Thus two right ascents become two right descents,
where the existing rank-matrix lifting theorem applies. The swap acts
on positions, so it commutes with value complementation.
-/

namespace Schubert.FinPermutation

variable {n : ℕ}

private theorem rightAdjacentSwap_trans_revPerm
    (w : FinPermutation n) (a : AdjacentPosition n) :
    rightAdjacentSwap (w.trans (Fin.revPerm : FinPermutation n)) a =
      (w.rightAdjacentSwap a).trans (Fin.revPerm : FinPermutation n) := by
  ext p
  rfl

theorem rightAdjacentSwap_strongBruhatLE_of_both_ascent
    {u v : FinPermutation n} (a : AdjacentPosition n)
    (huv : u ≤ᴮ v)
    (hu : u a.left < u a.right)
    (hv : v a.left < v a.right) :
    u.rightAdjacentSwap a ≤ᴮ v.rightAdjacentSwap a := by
  let c : FinPermutation n := Fin.revPerm
  have huc : HasDescent (u.trans c : FinPermutation n) a.left := by
    apply (hasDescent_left_iff (u.trans c) a).mpr
    change c (u a.right) < c (u a.left)
    simpa [c, Fin.revPerm_apply] using hu
  have hvc : HasDescent (v.trans c : FinPermutation n) a.left := by
    apply (hasDescent_left_iff (v.trans c) a).mpr
    change c (v a.right) < c (v a.left)
    simpa [c, Fin.revPerm_apply] using hv
  have hdual : v.trans c ≤ᴮ u.trans c :=
    (strongBruhatLE_iff_trans_revPerm_reverse u v).mp huv
  have hswap := rightAdjacentSwap_strongBruhatLE_of_both_descent
    a hdual hvc huc
  rw [rightAdjacentSwap_trans_revPerm,
    rightAdjacentSwap_trans_revPerm] at hswap
  exact (strongBruhatLE_iff_trans_revPerm_reverse
    (u.rightAdjacentSwap a) (v.rightAdjacentSwap a)).mpr hswap

end Schubert.FinPermutation
