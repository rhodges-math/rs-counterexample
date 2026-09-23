import Schubert.TypeA.Permutations.AdjacentTranspositions
import Schubert.TypeA.Permutations.EssentialSet

/-!
# Strict Bruhat comparison and covers

The definitions use the already verified rank-matrix partial order.  The final
lemmas isolate the exact order-theoretic fact used in the proof for essential
permutations: every proper lower neighbor of an essential permutation belongs
to the principal interval below the ambient permutation.
-/

namespace Schubert

namespace FinPermutation

variable {n : ℕ}

/-- Strict strong Bruhat comparison. -/
def StrongBruhatLT (u v : FinPermutation n) : Prop :=
  u ≤ᴮ v ∧ u ≠ v

infix:50 " <ᴮ " => StrongBruhatLT

theorem strongBruhatLT_irrefl (w : FinPermutation n) : ¬ w <ᴮ w := by
  intro h
  exact h.2 rfl

theorem strongBruhatLT_trans {u v w : FinPermutation n}
    (huv : u <ᴮ v) (hvw : v <ᴮ w) : u <ᴮ w := by
  refine ⟨strongBruhat_trans huv.1 hvw.1, ?_⟩
  intro huw
  have hwv : w ≤ᴮ v := by simpa [huw] using huv.1
  exact hvw.2 (strongBruhat_antisymm hvw.1 hwv)

/-- `u` is covered by `v` when it is strictly below `v` and the closed
interval between them has no third element. -/
def IsBruhatCover (u v : FinPermutation n) : Prop :=
  u <ᴮ v ∧
    ∀ z : FinPermutation n, u ≤ᴮ z → z ≤ᴮ v → z = u ∨ z = v

theorem IsBruhatCover.lt {u v : FinPermutation n} (h : IsBruhatCover u v) :
    u <ᴮ v :=
  h.1

theorem IsBruhatCover.le {u v : FinPermutation n} (h : IsBruhatCover u v) :
    u ≤ᴮ v :=
  h.1.1

theorem IsBruhatCover.ne {u v : FinPermutation n} (h : IsBruhatCover u v) :
    u ≠ v :=
  h.1.2

/-- A permutation agreeing with `w` away from two adjacent positions is
either `w` or the permutation obtained by swapping those positions. -/
private theorem eq_or_eq_rightAdjacentSwap_of_eq_outside
    (w z : FinPermutation n) (a : AdjacentPosition n)
    (houtside : ∀ k, k ≠ a.left → k ≠ a.right → z k = w k) :
    z = w ∨ z = w.rightAdjacentSwap a := by
  have hspecial (x : Fin n) (hx : x = a.left ∨ x = a.right) :
      z x = w a.left ∨ z x = w a.right := by
    let j := w.symm (z x)
    have hwj : w j = z x := by simp [j]
    by_cases hjl : j = a.left
    · left
      simpa [hjl] using hwj.symm
    · by_cases hjr : j = a.right
      · right
        simpa [hjr] using hwj.symm
      · have hzj : z j = w j := houtside j hjl hjr
        have hjx : j = x := z.injective (hzj.trans hwj)
        rcases hx with rfl | rfl <;> contradiction
  rcases hspecial a.left (Or.inl rfl) with hll | hlr
  · left
    apply Equiv.ext
    intro k
    by_cases hkl : k = a.left
    · simpa [hkl] using hll
    · by_cases hkr : k = a.right
      · subst k
        rcases hspecial a.right (Or.inr rfl) with hrl | hrr
        · exact False.elim (a.left_ne_right (z.injective (hrl.trans hll.symm)).symm)
        · exact hrr
      · exact houtside k hkl hkr
  · right
    apply Equiv.ext
    intro k
    by_cases hkl : k = a.left
    · subst k
      simpa using hlr
    · by_cases hkr : k = a.right
      · subst k
        rcases hspecial a.right (Or.inr rfl) with hrl | hrr
        · simpa using hrl
        · exact False.elim (a.left_ne_right (z.injective (hrr.trans hlr.symm)).symm)
      · rw [rightAdjacentSwap_apply_of_ne w a k hkl hkr]
        exact houtside k hkl hkr

/-- Every permutation in the interval between a right-descent swap and the
original permutation is one of the two endpoints. -/
theorem eq_swap_or_eq_of_between_rightDescent
    (v z : FinPermutation n) (a : AdjacentPosition n)
    (hdescent : v.HasDescent a.left)
    (hsz : v.rightAdjacentSwap a ≤ᴮ z) (hzv : z ≤ᴮ v) :
    z = v.rightAdjacentSwap a ∨ z = v := by
  have hrow (p : Fin n) (hp : p ≠ a.left) :
      ∀ q, z.bruhatRank p q = v.bruhatRank p q := by
    intro q
    have hswap := bruhatRank_rightAdjacentSwap_eq_of_ne v a p q hp
    exact Nat.le_antisymm (hzv p q) (by simpa [hswap] using hsz p q)
  have hbefore : ∀ k, k < a.left → z k = v k := by
    intro k hk
    let rec aux (x : Fin n) (hxk : x ≤ k) : z x = v x := by
      apply eq_at_of_bruhatRank_row_eq_of_eq_before x
      · apply hrow x
        exact ne_of_lt (lt_of_le_of_lt hxk hk)
      · intro y hyx
        exact aux y (hyx.le.trans hxk)
    termination_by x
    exact aux k le_rfl
  have hafter : ∀ k, a.right < k → z k = v k := by
    intro k hk
    have hkzero : 0 < k.1 := by
      have : 0 ≤ a.right.1 := Nat.zero_le _
      omega
    let b := AdjacentPosition.endingAt k hkzero
    have hbleft : b.left ≠ a.left := by
      intro heq
      have hval := congrArg Fin.val heq
      simp [b, AdjacentPosition.endingAt] at hval
      have hkval : a.left.1 + 1 < k.1 := hk
      omega
    have hbright : b.right ≠ a.left := by
      rw [AdjacentPosition.endingAt_right k hkzero]
      exact ne_of_gt (a.left_lt_right.trans hk)
    have heq := eq_right_of_bruhatRank_rows_eq z v b
      (hrow b.left hbleft) (hrow b.right hbright)
    rw [AdjacentPosition.endingAt_right k hkzero] at heq
    exact heq
  have houtside : ∀ k, k ≠ a.left → k ≠ a.right → z k = v k := by
    intro k hkl hkr
    rcases lt_or_gt_of_ne hkl with hklt | hkgt
    · exact hbefore k hklt
    · have hright : a.right < k := by
        change a.left.1 + 1 < k.1
        change a.left.1 < k.1 at hkgt
        have hkval : k.1 ≠ a.left.1 + 1 := by
          intro heq
          exact hkr (Fin.ext heq)
        omega
      exact hafter k hright
  rcases eq_or_eq_rightAdjacentSwap_of_eq_outside v z a houtside with rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- Swapping an adjacent right descent produces a lower cover in strong
Bruhat order. -/
theorem rightAdjacentSwap_isBruhatCover_of_descent
    (v : FinPermutation n) (a : AdjacentPosition n)
    (hdescent : v.HasDescent a.left) :
    IsBruhatCover (v.rightAdjacentSwap a) v := by
  refine ⟨rightAdjacentSwap_lt_of_descent v a hdescent, ?_⟩
  intro z hsz hzv
  exact eq_swap_or_eq_of_between_rightDescent v z a hdescent hsz hzv

/-- Any proper element below an essential permutation lies below the ambient
permutation. -/
theorem le_ambient_of_lt_essential
    {w v u : FinPermutation n} (hv : v ∈ w.essentialSet)
    (huv : u <ᴮ v) : u ≤ᴮ w :=
  hv.2 u huv.1 huv.2

/-- In particular, every lower Bruhat cover of an essential permutation lies
below the ambient permutation. -/
theorem le_ambient_of_cover_essential
    {w v u : FinPermutation n} (hv : v ∈ w.essentialSet)
    (huv : IsBruhatCover u v) : u ≤ᴮ w :=
  le_ambient_of_lt_essential hv huv.lt

/-- The global adjacent-descent cover property. -/
def AdjacentDescentCoverProperty (n : ℕ) : Prop :=
  ∀ (v : FinPermutation n) (a : AdjacentPosition n),
    v.HasDescent a.left → IsBruhatCover (v.rightAdjacentSwap a) v

/-- The adjacent-descent cover property holds for every finite symmetric
group. -/
theorem adjacentDescentCoverProperty (n : ℕ) :
    AdjacentDescentCoverProperty n :=
  fun v a ↦ rightAdjacentSwap_isBruhatCover_of_descent v a

/-- Every descent swap of an essential permutation lies below the ambient
permutation. -/
theorem rightDescentSwap_le_ambient_of_essential
    {w v : FinPermutation n} (hv : v ∈ w.essentialSet)
    (a : AdjacentPosition n) (hdescent : v.HasDescent a.left) :
    v.rightAdjacentSwap a ≤ᴮ w :=
  le_ambient_of_cover_essential hv
    (rightAdjacentSwap_isBruhatCover_of_descent v a hdescent)

end FinPermutation

end Schubert
