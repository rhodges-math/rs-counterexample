import Schubert.TypeA.Permutations.Bruhat

/-!
# Adjacent transpositions

This file defines adjacent positions without imposing an artificial
positivity hypothesis on `n`.  It then records right multiplication (swapping
adjacent positions) and left multiplication (swapping adjacent values).
-/

namespace Schubert

namespace FinPermutation

variable {n : ℕ}

/-- A position of `Fin n` which has an immediate right neighbor. -/
structure AdjacentPosition (n : ℕ) where
  left : Fin n
  hasRight : left.1 + 1 < n

@[ext]
theorem AdjacentPosition.ext {a b : AdjacentPosition n}
    (h : a.left = b.left) : a = b := by
  cases a
  cases b
  cases h
  rfl

namespace AdjacentPosition

/-- The immediate right neighbor of an adjacent position. -/
def right (a : AdjacentPosition n) : Fin n :=
  ⟨a.left.1 + 1, a.hasRight⟩

@[simp]
theorem right_val (a : AdjacentPosition n) : a.right.1 = a.left.1 + 1 :=
  rfl

theorem left_lt_right (a : AdjacentPosition n) : a.left < a.right := by
  exact Nat.lt_succ_self a.left.1

theorem left_ne_right (a : AdjacentPosition n) : a.left ≠ a.right :=
  a.left_lt_right.ne

/-- The adjacent position whose right endpoint is a given nonzero position. -/
def endingAt (k : Fin n) (hk : 0 < k.1) : AdjacentPosition n where
  left := ⟨k.1 - 1, by omega⟩
  hasRight := by
    rw [Nat.sub_add_cancel (by omega : 1 ≤ k.1)]
    exact k.2

@[simp]
theorem endingAt_right (k : Fin n) (hk : 0 < k.1) :
    (endingAt k hk).right = k := by
  apply Fin.ext
  exact Nat.sub_add_cancel (by omega : 1 ≤ k.1)

end AdjacentPosition

/-- The adjacent transposition exchanging `a.left` and `a.right`. -/
def adjacentTransposition (a : AdjacentPosition n) : FinPermutation n :=
  Equiv.swap a.left a.right

/-- Right multiplication by an adjacent transposition: exchange the entries
at two adjacent positions. -/
def rightAdjacentSwap (w : FinPermutation n) (a : AdjacentPosition n) :
    FinPermutation n :=
  (adjacentTransposition a).trans w

/-- Left multiplication by an adjacent transposition: exchange two adjacent
values wherever they occur. -/
def leftAdjacentSwap (w : FinPermutation n) (a : AdjacentPosition n) :
    FinPermutation n :=
  w.trans (adjacentTransposition a)

@[simp]
theorem rightAdjacentSwap_apply_left
    (w : FinPermutation n) (a : AdjacentPosition n) :
    w.rightAdjacentSwap a a.left = w a.right := by
  simp [rightAdjacentSwap, adjacentTransposition, Equiv.swap_apply_left]

@[simp]
theorem rightAdjacentSwap_apply_right
    (w : FinPermutation n) (a : AdjacentPosition n) :
    w.rightAdjacentSwap a a.right = w a.left := by
  simp [rightAdjacentSwap, adjacentTransposition, Equiv.swap_apply_right]

theorem rightAdjacentSwap_apply_of_ne
    (w : FinPermutation n) (a : AdjacentPosition n) (k : Fin n)
    (hleft : k ≠ a.left) (hright : k ≠ a.right) :
    w.rightAdjacentSwap a k = w k := by
  simp [rightAdjacentSwap, adjacentTransposition,
    Equiv.swap_apply_of_ne_of_ne hleft hright]

@[simp]
theorem leftAdjacentSwap_apply
    (w : FinPermutation n) (a : AdjacentPosition n) (k : Fin n) :
    w.leftAdjacentSwap a k = adjacentTransposition a (w k) :=
  rfl

/-- Swapping genuinely adjacent positions always changes a permutation. -/
theorem rightAdjacentSwap_ne
    (w : FinPermutation n) (a : AdjacentPosition n) :
    w.rightAdjacentSwap a ≠ w := by
  intro h
  have happly := DFunLike.congr_fun h a.left
  simp only [rightAdjacentSwap_apply_left] at happly
  exact a.left_ne_right (w.injective happly.symm)

/-- Swapping genuinely adjacent values always changes a permutation. -/
theorem leftAdjacentSwap_ne
    (w : FinPermutation n) (a : AdjacentPosition n) :
    w.leftAdjacentSwap a ≠ w := by
  intro h
  have happly := DFunLike.congr_fun h (w.symm a.left)
  simp [leftAdjacentSwap, adjacentTransposition] at happly
  exact a.left_ne_right happly.symm

/-- The paper's descent predicate at `a.left` is the usual adjacent
inequality. -/
theorem hasDescent_left_iff
    (w : FinPermutation n) (a : AdjacentPosition n) :
    w.HasDescent a.left ↔ w a.right < w a.left := by
  constructor
  · rintro ⟨j, hj, hdesc⟩
    have hja : j = a.right := Fin.ext hj
    simpa [hja] using hdesc
  · intro hdesc
    exact ⟨a.right, rfl, hdesc⟩

/-- A right descent is equivalently the assertion that the two values become
increasing after the adjacent position swap. -/
theorem hasDescent_iff_swap_increasing
    (w : FinPermutation n) (a : AdjacentPosition n) :
    w.HasDescent a.left ↔
      w.rightAdjacentSwap a a.left < w.rightAdjacentSwap a a.right := by
  simp [hasDescent_left_iff]

/-- Away from the cut immediately after `a.left`, the adjacent transposition
preserves every initial segment. -/
theorem adjacentTransposition_le_iff
    (a : AdjacentPosition n) (p k : Fin n) (hp : p ≠ a.left) :
    adjacentTransposition a k ≤ p ↔ k ≤ p := by
  have hp_cases : p < a.left ∨ a.right ≤ p := by
    rcases lt_or_gt_of_ne hp with h | h
    · exact Or.inl h
    · right
      change a.left.1 + 1 ≤ p.1
      omega
  rcases hp_cases with hpbelow | hpabove
  · by_cases hleft : k = a.left
    · subst k
      simp [adjacentTransposition, Equiv.swap_apply_left,
        not_le_of_gt hpbelow,
        not_le_of_gt (hpbelow.trans a.left_lt_right)]
    · by_cases hright : k = a.right
      · subst k
        simp [adjacentTransposition, Equiv.swap_apply_right,
          not_le_of_gt hpbelow,
          not_le_of_gt (hpbelow.trans a.left_lt_right)]
      · simp [adjacentTransposition,
          Equiv.swap_apply_of_ne_of_ne hleft hright]
  · by_cases hleft : k = a.left
    · subst k
      simp [adjacentTransposition, Equiv.swap_apply_left,
        a.left_lt_right.le.trans hpabove, hpabove]
    · by_cases hright : k = a.right
      · subst k
        simp [adjacentTransposition, Equiv.swap_apply_right,
          a.left_lt_right.le.trans hpabove, hpabove]
      · simp [adjacentTransposition,
          Equiv.swap_apply_of_ne_of_ne hleft hright]

/-- Except at the threshold `a.right`, swapping the two adjacent values
preserves membership in every upper interval. -/
theorem le_adjacentTransposition_iff
    (a : AdjacentPosition n) (q x : Fin n) (hq : q ≠ a.right) :
    q ≤ adjacentTransposition a x ↔ q ≤ x := by
  rcases lt_or_gt_of_ne hq with hqbelow | hqabove
  · have hqleft : q ≤ a.left := by
      change q.1 ≤ a.left.1
      change q.1 < a.left.1 + 1 at hqbelow
      omega
    by_cases hleft : x = a.left
    · subst x
      simp [adjacentTransposition, Equiv.swap_apply_left,
        hqleft, hqleft.trans a.left_lt_right.le]
    · by_cases hright : x = a.right
      · subst x
        simp [adjacentTransposition, Equiv.swap_apply_right,
          hqleft, hqleft.trans a.left_lt_right.le]
      · simp [adjacentTransposition,
          Equiv.swap_apply_of_ne_of_ne hleft hright]
  · have hleftq : a.left < q := a.left_lt_right.trans hqabove
    by_cases hleft : x = a.left
    · subst x
      simp [adjacentTransposition, Equiv.swap_apply_left,
        not_le_of_gt hqabove, not_le_of_gt hleftq]
    · by_cases hright : x = a.right
      · subst x
        simp [adjacentTransposition, Equiv.swap_apply_right,
          not_le_of_gt hqabove, not_le_of_gt hleftq]
      · simp [adjacentTransposition,
          Equiv.swap_apply_of_ne_of_ne hleft hright]

set_option backward.isDefEq.respectTransparency.types false in
/-- A left adjacent swap changes only the rank column at the upper of the two
adjacent values. -/
theorem bruhatRank_leftAdjacentSwap_eq_of_ne
    (w : FinPermutation n) (a : AdjacentPosition n)
    (p q : Fin n) (hq : q ≠ a.right) :
    (w.leftAdjacentSwap a).bruhatRank p q = w.bruhatRank p q := by
  classical
  unfold bruhatRank
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    leftAdjacentSwap_apply]
  rw [le_adjacentTransposition_iff a q (w k) hq]

set_option backward.isDefEq.respectTransparency.types false in
/-- At the unique changed rank column, an inverse descent makes the left
adjacent value swap no larger than the original rank. -/
theorem bruhatRank_leftAdjacentSwap_le_at_right
    (w : FinPermutation n) (a : AdjacentPosition n)
    (hdescent : HasDescent (w.symm : FinPermutation n) a.left) (p : Fin n) :
    (w.leftAdjacentSwap a).bruhatRank p a.right ≤
      w.bruhatRank p a.right := by
  classical
  let lowPos : Fin n := w.symm a.left
  let highPos : Fin n := w.symm a.right
  let S := Finset.univ.filter fun k : Fin n ↦
    k ≤ p ∧ a.right ≤ w.leftAdjacentSwap a k
  let T := Finset.univ.filter fun k : Fin n ↦
    k ≤ p ∧ a.right ≤ w k
  let f : Fin n → Fin n := fun k ↦ if k = lowPos then highPos else k
  have hpos : highPos < lowPos := by
    simpa [lowPos, highPos] using
      (hasDescent_left_iff (w.symm : FinPermutation n) a).mp hdescent
  have hhigh_not : highPos ∉ S := by
    simp [S, highPos, leftAdjacentSwap, adjacentTransposition,
      not_le_of_gt a.left_lt_right]
  have hmaps : Set.MapsTo f (S : Set (Fin n)) (T : Set (Fin n)) := by
    intro k hk
    have hkS : k ≤ p ∧ a.right ≤ w.leftAdjacentSwap a k := by
      simpa [S] using hk
    by_cases hklow : k = lowPos
    · subst k
      have hhighle : highPos ≤ p := hpos.le.trans hkS.1
      simp [f, T, highPos, hhighle]
    · have hwleft : w k ≠ a.left := by
        intro hw
        apply hklow
        apply w.injective
        simpa [lowPos] using hw
      have hwright_or : w k = a.right ∨ w k ≠ a.right :=
        eq_or_ne (w k) a.right
      rcases hwright_or with hwright | hwright
      · have : ¬ a.right ≤ w.leftAdjacentSwap a k := by
          simp [leftAdjacentSwap, adjacentTransposition, hwright,
            not_le_of_gt a.left_lt_right]
        exact False.elim (this hkS.2)
      · have hsame : w.leftAdjacentSwap a k = w k := by
          simp [leftAdjacentSwap, adjacentTransposition,
            Equiv.swap_apply_of_ne_of_ne hwleft hwright]
        simp [f, hklow, T, hkS.1, hsame] at hkS ⊢
        exact hkS
  have hinj : (S : Set (Fin n)).InjOn f := by
    intro x hx y hy hxy
    by_cases hxlow : x = lowPos
    · subst x
      by_cases hylow : y = lowPos
      · exact hylow.symm
      · have : y = highPos := by simpa [f, hylow] using hxy.symm
        subst y
        exact False.elim (hhigh_not hy)
    · by_cases hylow : y = lowPos
      · subst y
        have : x = highPos := by simpa [f, hxlow] using hxy
        subst x
        exact False.elim (hhigh_not hx)
      · simpa [f, hxlow, hylow] using hxy
  change S.card ≤ T.card
  exact Finset.card_le_card_of_injOn f hmaps hinj

/-- Swapping adjacent values at a descent of the inverse moves weakly
downward in strong Bruhat order. -/
theorem leftAdjacentSwap_le_of_inverseDescent
    (w : FinPermutation n) (a : AdjacentPosition n)
    (hdescent : HasDescent (w.symm : FinPermutation n) a.left) :
    w.leftAdjacentSwap a ≤ᴮ w := by
  intro p q
  by_cases hq : q = a.right
  · subst q
    exact bruhatRank_leftAdjacentSwap_le_at_right w a hdescent p
  · exact (bruhatRank_leftAdjacentSwap_eq_of_ne w a p q hq).le

/-- Swapping adjacent values at an inverse descent moves strictly downward. -/
theorem leftAdjacentSwap_lt_of_inverseDescent
    (w : FinPermutation n) (a : AdjacentPosition n)
    (hdescent : HasDescent (w.symm : FinPermutation n) a.left) :
    StrongBruhatLE (w.leftAdjacentSwap a) w ∧ w.leftAdjacentSwap a ≠ w :=
  ⟨leftAdjacentSwap_le_of_inverseDescent w a hdescent,
    leftAdjacentSwap_ne w a⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The rank rows of an adjacent position swap agree away from the cut at
`a.left`. -/
theorem bruhatRank_rightAdjacentSwap_eq_of_ne
    (w : FinPermutation n) (a : AdjacentPosition n)
    (p q : Fin n) (hp : p ≠ a.left) :
    (w.rightAdjacentSwap a).bruhatRank p q = w.bruhatRank p q := by
  classical
  unfold bruhatRank
  apply Finset.card_equiv (adjacentTransposition a)
  intro k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    rightAdjacentSwap, Equiv.trans_apply]
  rw [adjacentTransposition_le_iff a p k hp]

/-- At the unique changed rank row, a descent makes the swapped rank no
larger than the original rank. -/
theorem bruhatRank_rightAdjacentSwap_le_at_left
    (w : FinPermutation n) (a : AdjacentPosition n)
    (hdescent : w.HasDescent a.left) (q : Fin n) :
    (w.rightAdjacentSwap a).bruhatRank a.left q ≤
      w.bruhatRank a.left q := by
  classical
  unfold bruhatRank
  apply Finset.card_le_card
  intro k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rintro ⟨hkle, hq⟩
  by_cases hleft : k = a.left
  · subst k
    refine ⟨le_rfl, ?_⟩
    rw [rightAdjacentSwap_apply_left] at hq
    exact hq.trans (hasDescent_left_iff w a |>.mp hdescent).le
  · have hright : k ≠ a.right := by
      intro h
      subst k
      exact (not_le_of_gt a.left_lt_right) hkle
    refine ⟨hkle, ?_⟩
    simpa [rightAdjacentSwap_apply_of_ne w a k hleft hright] using hq

/-- Swapping a right descent moves weakly downward in strong Bruhat order. -/
theorem rightAdjacentSwap_le_of_descent
    (w : FinPermutation n) (a : AdjacentPosition n)
    (hdescent : w.HasDescent a.left) :
    w.rightAdjacentSwap a ≤ᴮ w := by
  intro p q
  by_cases hp : p = a.left
  · subst p
    exact bruhatRank_rightAdjacentSwap_le_at_left w a hdescent q
  · exact (bruhatRank_rightAdjacentSwap_eq_of_ne w a p q hp).le

/-- Swapping a right descent moves strictly downward in strong Bruhat order. -/
theorem rightAdjacentSwap_lt_of_descent
    (w : FinPermutation n) (a : AdjacentPosition n)
    (hdescent : w.HasDescent a.left) :
    StrongBruhatLE (w.rightAdjacentSwap a) w ∧ w.rightAdjacentSwap a ≠ w :=
  ⟨rightAdjacentSwap_le_of_descent w a hdescent,
    rightAdjacentSwap_ne w a⟩

/-- Passing across one adjacent position adds exactly the indicator of the new
entry to every southwest rank number. -/
theorem bruhatRank_right_eq_left_add_ite
    (w : FinPermutation n) (a : AdjacentPosition n) (q : Fin n) :
    w.bruhatRank a.right q =
      w.bruhatRank a.left q + if q ≤ w a.right then 1 else 0 := by
  classical
  let R := Finset.univ.filter fun k : Fin n ↦ k ≤ a.right ∧ q ≤ w k
  let L := Finset.univ.filter fun k : Fin n ↦ k ≤ a.left ∧ q ≤ w k
  by_cases hq : q ≤ w a.right
  · have hset : R = insert a.right L := by
      ext k
      simp only [R, L, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert]
      constructor
      · rintro ⟨hkr, hqk⟩
        by_cases hk : k = a.right
        · exact Or.inl hk
        · right
          refine ⟨?_, hqk⟩
          change k.1 ≤ a.left.1
          change k.1 ≤ a.left.1 + 1 at hkr
          have hkval : k.1 ≠ a.left.1 + 1 := by
            intro heq
            exact hk (Fin.ext heq)
          omega
      · rintro (rfl | ⟨hkl, hqk⟩)
        · exact ⟨le_rfl, hq⟩
        · exact ⟨hkl.trans a.left_lt_right.le, hqk⟩
    have hnotmem : a.right ∉ L := by
      simp [L, not_le_of_gt a.left_lt_right]
    simp [bruhatRank, R, L, hq, hset,
      Finset.card_insert_of_notMem hnotmem]
  · have hset : R = L := by
      ext k
      simp only [R, L, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hkr, hqk⟩
        refine ⟨?_, hqk⟩
        change k.1 ≤ a.left.1
        change k.1 ≤ a.left.1 + 1 at hkr
        have hkval : k.1 ≠ a.left.1 + 1 := by
          intro heq
          have hk : k = a.right := Fin.ext heq
          subst k
          exact hq hqk
        omega
      · rintro ⟨hkl, hqk⟩
        exact ⟨hkl.trans a.left_lt_right.le, hqk⟩
    simp [bruhatRank, R, L, hq, hset]

/-- Two consecutive equal rank rows determine the entry added in the second
row. -/
theorem eq_right_of_bruhatRank_rows_eq
    (u v : FinPermutation n) (a : AdjacentPosition n)
    (hleft : ∀ q, u.bruhatRank a.left q = v.bruhatRank a.left q)
    (hright : ∀ q, u.bruhatRank a.right q = v.bruhatRank a.right q) :
    u a.right = v a.right := by
  apply le_antisymm
  · by_contra h
    have hlt : v a.right < u a.right := lt_of_not_ge h
    have hu := bruhatRank_right_eq_left_add_ite u a (u a.right)
    have hv := bruhatRank_right_eq_left_add_ite v a (u a.right)
    rw [if_pos le_rfl] at hu
    rw [if_neg (not_le_of_gt hlt)] at hv
    have hl := hleft (u a.right)
    have hr := hright (u a.right)
    omega
  · by_contra h
    have hlt : u a.right < v a.right := lt_of_not_ge h
    have hu := bruhatRank_right_eq_left_add_ite u a (v a.right)
    have hv := bruhatRank_right_eq_left_add_ite v a (v a.right)
    rw [if_neg (not_le_of_gt hlt)] at hu
    rw [if_pos le_rfl] at hv
    have hl := hleft (v a.right)
    have hr := hright (v a.right)
    omega

end FinPermutation

end Schubert
