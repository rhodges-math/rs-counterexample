import Schubert.TypeA.Permutations.BruhatCovers
import Schubert.TypeA.Permutations.AdjacentLength

/-!
# Coxeter length grades strong Bruhat order

This file proves directly from the rank-matrix definition that strong Bruhat
order on finite permutations is graded by inversion length.  The key input is
the adjacent lifting property.  Keeping this argument local avoids importing
an abstract Coxeter-group model merely to compare the two concrete notions.
-/

namespace Schubert

namespace FinPermutation

variable {n : ℕ}

/-- The contribution to a southwest rank strictly before one position. -/
private def bruhatRankBefore (w : FinPermutation n) (p q : Fin n) : ℕ :=
  (Finset.univ.filter fun k ↦ k < p ∧ q ≤ w k).card

/-- A rank row is its strict-prefix contribution plus the indicator of its
last entry. -/
private theorem bruhatRank_eq_before_add_ite
    (w : FinPermutation n) (p q : Fin n) :
    w.bruhatRank p q =
      bruhatRankBefore w p q + if q ≤ w p then 1 else 0 := by
  classical
  unfold bruhatRank bruhatRankBefore
  by_cases hq : q ≤ w p
  · have hset :
        Finset.univ.filter (fun k : Fin n ↦ k ≤ p ∧ q ≤ w k) =
          insert p (Finset.univ.filter fun k : Fin n ↦ k < p ∧ q ≤ w k) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert]
      constructor
      · rintro ⟨hkp, hqk⟩
        rcases hkp.eq_or_lt with rfl | hkp
        · exact Or.inl rfl
        · exact Or.inr ⟨hkp, hqk⟩
      · rintro (rfl | ⟨hkp, hqk⟩)
        · exact ⟨le_rfl, hq⟩
        · exact ⟨hkp.le, hqk⟩
    have hpnot :
        p ∉ Finset.univ.filter (fun k : Fin n ↦ k < p ∧ q ≤ w k) := by
      simp
    rw [hset, Finset.card_insert_of_notMem hpnot, if_pos hq]
  · have hset :
        Finset.univ.filter (fun k : Fin n ↦ k ≤ p ∧ q ≤ w k) =
          Finset.univ.filter fun k : Fin n ↦ k < p ∧ q ≤ w k := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hkp, hqk⟩
        refine ⟨lt_of_le_of_ne hkp ?_, hqk⟩
        intro hkp'
        subst k
        exact hq hqk
      · rintro ⟨hkp, hqk⟩
        exact ⟨hkp.le, hqk⟩
    rw [hset, if_neg hq]
    omega

/-- Bruhat comparison also compares the ranks in a strict position prefix. -/
private theorem bruhatRankBefore_le_of_strongBruhatLE
    {u v : FinPermutation n} (huv : u ≤ᴮ v) (p q : Fin n) :
    bruhatRankBefore u p q ≤ bruhatRankBefore v p q := by
  by_cases hp : p.1 = 0
  · have hempty (w : FinPermutation n) :
        Finset.univ.filter (fun k : Fin n ↦ k < p ∧ q ≤ w k) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      omega
    simp [bruhatRankBefore, hempty]
  · have hppos : 0 < p.1 := Nat.pos_of_ne_zero hp
    let a := AdjacentPosition.endingAt p hppos
    have h := huv a.left q
    have hset (w : FinPermutation n) :
        Finset.univ.filter (fun k : Fin n ↦ k < p ∧ q ≤ w k) =
          Finset.univ.filter (fun k : Fin n ↦ k ≤ a.left ∧ q ≤ w k) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change (k.1 < p.1 ∧ q ≤ w k) ↔
        (k.1 ≤ p.1 - 1 ∧ q ≤ w k)
      omega
    unfold bruhatRankBefore
    rw [hset u, hset v]
    exact h

/-- Swapping adjacent positions does not change the strict-prefix rank at
their left endpoint. -/
private theorem bruhatRankBefore_rightAdjacentSwap
    (w : FinPermutation n) (a : AdjacentPosition n) (q : Fin n) :
    bruhatRankBefore (w.rightAdjacentSwap a) a.left q =
      bruhatRankBefore w a.left q := by
  classical
  unfold bruhatRankBefore
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hk : k < a.left
  · have hkl : k ≠ a.left := ne_of_lt hk
    have hkr : k ≠ a.right := ne_of_lt (hk.trans a.left_lt_right)
    rw [rightAdjacentSwap_apply_of_ne w a k hkl hkr]
  · simp [hk]

/-- Right lifting when both endpoints have a descent at the chosen adjacent
position. -/
theorem rightAdjacentSwap_strongBruhatLE_of_both_descent
    {u v : FinPermutation n} (a : AdjacentPosition n)
    (huv : u ≤ᴮ v) (hu : u.HasDescent a.left)
    (hv : v.HasDescent a.left) :
    u.rightAdjacentSwap a ≤ᴮ v.rightAdjacentSwap a := by
  intro p q
  by_cases hp : p = a.left
  · subst p
    have hprefix := huv a.left q
    have hbefore := bruhatRankBefore_le_of_strongBruhatLE
      huv a.left q
    have hright := huv a.right q
    rw [bruhatRank_right_eq_left_add_ite,
      bruhatRank_right_eq_left_add_ite] at hright
    rw [bruhatRank_eq_before_add_ite,
      bruhatRank_eq_before_add_ite,
      bruhatRankBefore_rightAdjacentSwap,
      bruhatRankBefore_rightAdjacentSwap,
      rightAdjacentSwap_apply_left,
      rightAdjacentSwap_apply_left]
    rw [bruhatRank_eq_before_add_ite,
      bruhatRank_eq_before_add_ite] at hright
    have huval := (hasDescent_left_iff u a).mp hu
    have hvval := (hasDescent_left_iff v a).mp hv
    by_cases hul : q ≤ u a.left <;>
      by_cases hur : q ≤ u a.right <;>
      by_cases hvl : q ≤ v a.left <;>
      by_cases hvr : q ≤ v a.right <;>
      simp [hul, hur, hvl, hvr] at hprefix hbefore hright ⊢ <;>
      omega
  · rw [bruhatRank_rightAdjacentSwap_eq_of_ne u a p q hp,
      bruhatRank_rightAdjacentSwap_eq_of_ne v a p q hp]
    exact huv p q

/-- Right lifting when the lower endpoint has an ascent and the upper
endpoint has a descent. -/
theorem strongBruhatLE_rightAdjacentSwap_of_ascent_descent
    {u v : FinPermutation n} (a : AdjacentPosition n)
    (huv : u ≤ᴮ v) (hu : u a.left < u a.right)
    (hv : v.HasDescent a.left) :
    u ≤ᴮ v.rightAdjacentSwap a := by
  intro p q
  by_cases hp : p = a.left
  · subst p
    have hleft := huv a.left q
    have hright := huv a.right q
    have hbefore := bruhatRankBefore_le_of_strongBruhatLE
      huv a.left q
    rw [bruhatRank_right_eq_left_add_ite,
      bruhatRank_right_eq_left_add_ite] at hright
    rw [bruhatRank_eq_before_add_ite,
      bruhatRank_eq_before_add_ite,
      bruhatRankBefore_rightAdjacentSwap,
      rightAdjacentSwap_apply_left]
    rw [bruhatRank_eq_before_add_ite,
      bruhatRank_eq_before_add_ite] at hleft hright
    have hvval := (hasDescent_left_iff v a).mp hv
    by_cases hul : q ≤ u a.left <;>
      by_cases hur : q ≤ u a.right <;>
      by_cases hvl : q ≤ v a.left <;>
      by_cases hvr : q ≤ v a.right <;>
      simp [hul, hur, hvl, hvr] at hleft hright hbefore ⊢ <;>
      omega
  · rw [bruhatRank_rightAdjacentSwap_eq_of_ne v a p q hp]
    exact huv p q

/-- Inversion length is monotone for strong Bruhat order. -/
theorem length_le_of_strongBruhatLE {u v : FinPermutation n}
    (huv : u ≤ᴮ v) : u.length ≤ v.length := by
  generalize hm : v.length = m
  induction m using Nat.strong_induction_on generalizing u v with
  | h m ih =>
      by_cases hvrefl : v = Equiv.refl (Fin n)
      · subst v
        have hueq : u = Equiv.refl (Fin n) :=
          strongBruhat_antisymm huv (refl_strongBruhatLE u)
        subst u
        simpa using Nat.zero_le m
      · obtain ⟨i, j, hj, hdescent⟩ := exists_descent_of_ne_refl v hvrefl
        let a : AdjacentPosition n :=
          { left := i
            hasRight := by
              rw [← hj]
              exact j.isLt }
        have ha : v.HasDescent a.left := ⟨j, hj, hdescent⟩
        have hvdrop := length_rightAdjacentSwap_of_descent v a ha
        have hvlt : (v.rightAdjacentSwap a).length < m := by omega
        rcases descent_or_ascent u a with hu | hu
        · have hswap := rightAdjacentSwap_strongBruhatLE_of_both_descent
              a huv hu ha
          have hind := ih (v.rightAdjacentSwap a).length hvlt hswap rfl
          have hudrop := length_rightAdjacentSwap_of_descent u a hu
          omega
        · have hbelow := strongBruhatLE_rightAdjacentSwap_of_ascent_descent
              a huv hu ha
          have hind := ih (v.rightAdjacentSwap a).length hvlt hbelow rfl
          omega

/-- Comparable permutations of equal Coxeter length are equal. -/
theorem eq_of_strongBruhatLE_of_length_eq {u v : FinPermutation n}
    (huv : u ≤ᴮ v) (hlength : u.length = v.length) : u = v := by
  generalize hm : v.length = m
  induction m using Nat.strong_induction_on generalizing u v with
  | h m ih =>
      by_cases hvrefl : v = Equiv.refl (Fin n)
      · subst v
        exact strongBruhat_antisymm huv (refl_strongBruhatLE u)
      · obtain ⟨i, j, hj, hdescent⟩ := exists_descent_of_ne_refl v hvrefl
        let a : AdjacentPosition n :=
          { left := i
            hasRight := by
              rw [← hj]
              exact j.isLt }
        have ha : v.HasDescent a.left := ⟨j, hj, hdescent⟩
        have hvdrop := length_rightAdjacentSwap_of_descent v a ha
        have hvlt : (v.rightAdjacentSwap a).length < m := by omega
        rcases descent_or_ascent u a with hu | hu
        · have hswap := rightAdjacentSwap_strongBruhatLE_of_both_descent
              a huv hu ha
          have hudrop := length_rightAdjacentSwap_of_descent u a hu
          have hslen : (u.rightAdjacentSwap a).length =
              (v.rightAdjacentSwap a).length := by omega
          have heq := ih (v.rightAdjacentSwap a).length hvlt
            hswap hslen rfl
          have hback := congrArg (fun z : FinPermutation n ↦
            z.rightAdjacentSwap a) heq
          simpa using hback
        · have hbelow := strongBruhatLE_rightAdjacentSwap_of_ascent_descent
              a huv hu ha
          have hle := length_le_of_strongBruhatLE hbelow
          omega

end FinPermutation

end Schubert
