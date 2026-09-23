import Schubert.TypeA.Permutations.BruhatCovers

/-!
# Essential permutations are bigrassmannian

This file proves the Reiner--Woo--Yong order-theoretic statement for the
rank-matrix model developed in this project.  The proof first shows that an
essential permutation has a unique right descent.  A value-swapping version
of the same argument gives a unique descent of its inverse.
-/

namespace Schubert

namespace FinPermutation

variable {n : ℕ}

/-- A strictly increasing finite permutation is the identity. -/
theorem eq_refl_of_strictMono (w : FinPermutation n) (hw : StrictMono w) :
    w = Equiv.refl (Fin n) := by
  apply Equiv.ext
  intro i
  apply wellFounded_lt.induction i
  intro i ih
  obtain ⟨j, hj⟩ := w.surjective i
  rcases lt_trichotomy j i with hji | hji | hij
  · have hjfix : w j = j := ih j hji
    have : j = i := hjfix ▸ hj
    exact False.elim (hji.ne this)
  · subst j
    simpa using hj
  · have hmono : w i < w j := hw hij
    rw [hj] at hmono
    have hfix : w (w i) = w i := ih (w i) hmono
    exact w.injective hfix

/-- A finite permutation with no descents is the identity. -/
theorem eq_refl_of_no_descent (w : FinPermutation n)
    (hdesc : ∀ i, ¬ w.HasDescent i) :
    w = Equiv.refl (Fin n) := by
  apply eq_refl_of_strictMono w
  cases n with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ m =>
      rw [Fin.strictMono_iff_lt_succ]
      intro i
      let a : AdjacentPosition (m + 1) :=
        { left := i.castSucc
          hasRight := by simp }
      have hnot : ¬ w a.right < w a.left :=
        (hasDescent_left_iff w a).not.mp (hdesc a.left)
      have hne : w a.left ≠ w a.right :=
        w.injective.ne a.left_ne_right
      have hlt : w a.left < w a.right :=
        lt_of_le_of_ne (le_of_not_gt hnot) hne
      change (w i.castSucc).val < (w i.succ).val
      change (w a.left).val < (w a.right).val at hlt
      have hright : a.right = i.succ := by
        apply Fin.ext
        rfl
      rw [hright] at hlt
      exact hlt

/-- Every nonidentity finite permutation has a descent. -/
theorem exists_descent_of_ne_refl (w : FinPermutation n)
    (hw : w ≠ Equiv.refl (Fin n)) :
    ∃ i, w.HasDescent i := by
  by_contra h
  push Not at h
  exact hw (eq_refl_of_no_descent w h)

/-- The identity permutation is the minimum of the rank-matrix strong Bruhat
order. -/
theorem refl_strongBruhatLE (w : FinPermutation n) :
    (Equiv.refl (Fin n) : FinPermutation n) ≤ᴮ w := by
  intro p q
  classical
  let P : Finset (Fin n) := Finset.Iic p
  let H : Finset (Fin n) := P.filter fun i ↦ q ≤ w i
  let L : Finset (Fin n) := P.filter fun i ↦ w i < q
  have hpartition : H.card + L.card = P.card := by
    simpa [H, L, not_le] using
      (Finset.card_filter_add_card_filter_not
        (s := P) (fun i : Fin n ↦ q ≤ w i))
  have hlow : L.card ≤ q.1 := by
    calc
      L.card = (L.image w).card :=
        (Finset.card_image_of_injective L w.injective).symm
      _ ≤ (Finset.Iio q).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_image] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        have hiL : w i < q := (by simpa [L] using hi : i ∈ P ∧ w i < q).2
        exact Finset.mem_Iio.mpr hiL
      _ = q.1 := Fin.card_Iio q
  have hPcard : P.card = p.1 + 1 := by
    simp [P]
  have hH : H.card = w.bruhatRank p q := by
    congr 1
    ext i
    simp [H, P]
  by_cases hqp : q ≤ p
  · have hid :
        bruhatRank (Equiv.refl (Fin n) : FinPermutation n) p q =
          p.1 - q.1 + 1 := by
      rw [bruhatRank]
      have hset :
          Finset.univ.filter
              (fun i : Fin n ↦ i ≤ p ∧ q ≤ (Equiv.refl (Fin n)) i) =
            Finset.Icc q p := by
        ext i
        simp [and_comm]
      rw [hset, Fin.card_Icc]
      omega
    rw [hid, ← hH]
    omega
  · have hid :
        bruhatRank (Equiv.refl (Fin n) : FinPermutation n) p q = 0 := by
      rw [bruhatRank]
      apply Finset.card_eq_zero.mpr
      ext x
      simp only [Finset.notMem_empty, iff_false, Finset.mem_filter,
        Finset.mem_univ, true_and, not_and]
      intro hxp
      exact not_le_of_gt (hxp.trans_lt (lt_of_not_ge hqp))
    simp [hid]

/-- An essential permutation is not the identity. -/
theorem ne_refl_of_mem_essentialSet
    {w v : FinPermutation n} (hv : v ∈ w.essentialSet) :
    v ≠ Equiv.refl (Fin n) := by
  intro h
  apply hv.1
  simpa [h] using refl_strongBruhatLE w

/-- An essential permutation has exactly one right descent. -/
theorem isGrassmannian_of_mem_essentialSet
    {w v : FinPermutation n} (hv : v ∈ w.essentialSet) :
    v.IsGrassmannian := by
  obtain ⟨i, hi⟩ := exists_descent_of_ne_refl v
    (ne_refl_of_mem_essentialSet hv)
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hij
  let a : AdjacentPosition n :=
    { left := i
      hasRight := by
        rcases hi with ⟨k, hk, _⟩
        omega }
  let b : AdjacentPosition n :=
    { left := j
      hasRight := by
        rcases hj with ⟨k, hk, _⟩
        omega }
  have hab : a.left ≠ b.left := by
    simpa [a, b] using (fun h : i = j ↦ hij h.symm)
  have haw : v.rightAdjacentSwap a ≤ᴮ w :=
    rightDescentSwap_le_ambient_of_essential hv a (by simpa [a] using hi)
  have hbw : v.rightAdjacentSwap b ≤ᴮ w :=
    rightDescentSwap_le_ambient_of_essential hv b (by simpa [b] using hj)
  apply hv.1
  intro p q
  by_cases hp : p = a.left
  · have hpb : p ≠ b.left := by simpa [hp] using hab
    rw [← bruhatRank_rightAdjacentSwap_eq_of_ne v b p q hpb]
    exact hbw p q
  · rw [← bruhatRank_rightAdjacentSwap_eq_of_ne v a p q hp]
    exact haw p q

/-- An essential permutation has exactly one inverse descent. -/
theorem inverse_isGrassmannian_of_mem_essentialSet
    {w v : FinPermutation n} (hv : v ∈ w.essentialSet) :
    IsGrassmannian (v.symm : FinPermutation n) := by
  have hvne := ne_refl_of_mem_essentialSet hv
  have hsymmne : (v.symm : FinPermutation n) ≠ Equiv.refl (Fin n) := by
    intro h
    apply hvne
    have hs := congrArg Equiv.symm h
    simpa using hs
  obtain ⟨i, hi⟩ := exists_descent_of_ne_refl
    (v.symm : FinPermutation n) hsymmne
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hij
  let a : AdjacentPosition n :=
    { left := i
      hasRight := by
        rcases hi with ⟨k, hk, _⟩
        omega }
  let b : AdjacentPosition n :=
    { left := j
      hasRight := by
        rcases hj with ⟨k, hk, _⟩
        omega }
  have hab : a.left ≠ b.left := by
    simpa [a, b] using (fun h : i = j ↦ hij h.symm)
  have habright : a.right ≠ b.right := by
    intro h
    apply hab
    apply Fin.ext
    have hval := congrArg Fin.val h
    simp only [AdjacentPosition.right_val] at hval
    omega
  have haw : v.leftAdjacentSwap a ≤ᴮ w :=
    le_ambient_of_lt_essential hv
      (leftAdjacentSwap_lt_of_inverseDescent v a (by simpa [a] using hi))
  have hbw : v.leftAdjacentSwap b ≤ᴮ w :=
    le_ambient_of_lt_essential hv
      (leftAdjacentSwap_lt_of_inverseDescent v b (by simpa [b] using hj))
  apply hv.1
  intro p q
  by_cases hq : q = a.right
  · have hqb : q ≠ b.right := by simpa [hq] using habright
    rw [← bruhatRank_leftAdjacentSwap_eq_of_ne v b p q hqb]
    exact hbw p q
  · rw [← bruhatRank_leftAdjacentSwap_eq_of_ne v a p q hq]
    exact haw p q

/-- Every essential permutation is bigrassmannian. -/
theorem mem_essentialSet_isBigrassmannian
    {w v : FinPermutation n} (hv : v ∈ w.essentialSet) :
    v.IsBigrassmannian :=
  ⟨isGrassmannian_of_mem_essentialSet hv,
    inverse_isGrassmannian_of_mem_essentialSet hv⟩

/-- The global Reiner--Woo--Yong essential-bigrassmannian property, proved
for every finite symmetric group. -/
theorem essentialBigrassmannianProperty (n : ℕ) :
    EssentialBigrassmannianProperty n :=
  fun _w _v hv ↦ mem_essentialSet_isBigrassmannian hv

end FinPermutation

end Schubert
