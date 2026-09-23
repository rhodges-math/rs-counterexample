import Schubert.RS.Support.BruhatRanks

/-!
# Elementary bounds for northwest rank matrices

Increasing either cutoff by one can add at most one permutation-matrix
entry.  Iterating these one-step estimates gives the integral Lipschitz
bounds used in the single-rank characterization of a bigrassmannian Bruhat
upper ideal.
-/

namespace Schubert

namespace FinPermutation

variable {n : ℕ}

/-- There are exactly `k` elements of `Fin n` whose values are below `k`. -/
theorem card_filter_fin_val_lt (k : ℕ) (hkn : k ≤ n) :
    (Finset.univ.filter fun i : Fin n ↦ i.1 < k).card = k := by
  classical
  let S := Finset.univ.filter fun i : Fin n ↦ i.1 < k
  calc
    S.card = (Finset.univ : Finset (Fin k)).card := by
      apply Finset.card_bij (fun i hi ↦ ⟨i.1, by
        simpa [S] using (Finset.mem_filter.mp hi).2⟩)
      · intro i hi
        simp
      · intro i hi j hj hij
        have hval : i.1 = j.1 :=
          congrArg (fun x : Fin k ↦ x.1) hij
        exact Fin.ext hval
      · intro j _
        let i : Fin n := ⟨j.1, j.2.trans_le hkn⟩
        refine ⟨i, ?_, Fin.ext rfl⟩
        simp [S, i]
    _ = k := by simp

/-- There are exactly `b-a` elements of `Fin n` in the half-open natural
interval `[a,b)`. -/
theorem card_filter_fin_val_Ico (a b : ℕ) (hab : a ≤ b) (hbn : b ≤ n) :
    (Finset.univ.filter fun i : Fin n ↦ a ≤ i.1 ∧ i.1 < b).card =
      b - a := by
  classical
  let L := Finset.univ.filter fun i : Fin n ↦ i.1 < a
  let M := Finset.univ.filter fun i : Fin n ↦ i.1 < b
  let I := Finset.univ.filter fun i : Fin n ↦ a ≤ i.1 ∧ i.1 < b
  have hdisjoint : Disjoint L I := by
    refine Finset.disjoint_left.mpr ?_
    intro i hiL hiI
    simp only [L, I, Finset.mem_filter, Finset.mem_univ, true_and] at hiL hiI
    omega
  have hunion : L ∪ I = M := by
    ext i
    simp only [L, I, M, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    omega
  have hL : L.card = a := by
    exact card_filter_fin_val_lt a (hab.trans hbn)
  have hM : M.card = b := card_filter_fin_val_lt b hbn
  have hcard := Finset.card_union_of_disjoint hdisjoint
  rw [hunion, hL, hM] at hcard
  change I.card = b - a
  omega

/-- If the northwest rank is smaller than the number of available rows,
some row before the position cutoff has value on or beyond the value
cutoff. -/
theorem exists_northeast_of_northwestRankNat_lt_left
    (w : FinPermutation n) (r s : ℕ) (hrn : r ≤ n)
    (h : northwestRankNat w r s < r) :
    ∃ i : Fin n, i.1 < r ∧ s ≤ (w i).1 := by
  classical
  by_contra hnone
  have hall : ∀ i : Fin n, i.1 < r → (w i).1 < s := by
    intro i hir
    by_contra hnot
    exact hnone ⟨i, hir, Nat.le_of_not_gt hnot⟩
  let A := Finset.univ.filter (fun i : Fin n ↦ i.1 < r)
  let B := Finset.univ.filter
    (fun i : Fin n ↦ i.1 < r ∧ (w i).1 < s)
  have hset : A = B := by
    ext i
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hir ↦ ⟨hir, hall i hir⟩, And.left⟩
  have hA : A.card = r := card_filter_fin_val_lt r hrn
  have hrank : northwestRankNat w r s = r := by
    change B.card = r
    rw [← hset, hA]
  omega

/-- If the northwest rank is smaller than the number of available values,
some value below the value cutoff occurs on or beyond the position cutoff. -/
theorem exists_southwest_of_northwestRankNat_lt_right
    (w : FinPermutation n) (r s : ℕ) (hsn : s ≤ n)
    (h : northwestRankNat w r s < s) :
    ∃ i : Fin n, r ≤ i.1 ∧ (w i).1 < s := by
  have hsymm :
      northwestRankNat (w.symm : FinPermutation n) s r < s := by
    simpa only [northwestRankNat_symm] using h
  obtain ⟨q, hqs, hqr⟩ :=
    exists_northeast_of_northwestRankNat_lt_left
      (w.symm : FinPermutation n) s r hsn hsymm
  refine ⟨w.symm q, hqr, ?_⟩
  simpa using hqs

/-- Northwest rank is monotone in the position cutoff. -/
theorem northwestRankNat_mono_left
    (w : FinPermutation n) (s : ℕ) {r R : ℕ} (hrR : r ≤ R) :
    northwestRankNat w r s ≤ northwestRankNat w R s := by
  classical
  unfold northwestRankNat
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact ⟨hi.1.trans_le hrR, hi.2⟩

/-- Northwest rank is monotone in the value cutoff. -/
theorem northwestRankNat_mono_right
    (w : FinPermutation n) (r : ℕ) {s S : ℕ} (hsS : s ≤ S) :
    northwestRankNat w r s ≤ northwestRankNat w r S := by
  classical
  unfold northwestRankNat
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact ⟨hi.1, hi.2.trans_le hsS⟩

/-- Northwest rank is monotone when both cutoffs grow. -/
theorem northwestRankNat_mono
    (w : FinPermutation n) {r s R S : ℕ} (hrR : r ≤ R) (hsS : s ≤ S) :
    northwestRankNat w r s ≤ northwestRankNat w R S :=
  (northwestRankNat_mono_left w s hrR).trans
    (northwestRankNat_mono_right w R hsS)

/-- Adding one position to a northwest rectangle increases its rank by at
most one. -/
theorem northwestRankNat_succ_left_le
    (w : FinPermutation n) (r s : ℕ) (hr : r < n) :
    northwestRankNat w (r + 1) s ≤ northwestRankNat w r s + 1 := by
  classical
  let k : Fin n := ⟨r, hr⟩
  let A := Finset.univ.filter
    (fun i : Fin n ↦ i.1 < r + 1 ∧ (w i).1 < s)
  let B := Finset.univ.filter
    (fun i : Fin n ↦ i.1 < r ∧ (w i).1 < s)
  have hsubset : A ⊆ insert k B := by
    intro i hi
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    by_cases hir : i.1 = r
    · exact Finset.mem_insert.mpr (Or.inl (Fin.ext hir))
    · exact Finset.mem_insert.mpr (Or.inr (by
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨by omega, hi.2⟩))
  calc
    northwestRankNat w (r + 1) s = A.card := rfl
    _ ≤ (insert k B).card := Finset.card_le_card hsubset
    _ ≤ B.card + 1 := Finset.card_insert_le k B
    _ = northwestRankNat w r s + 1 := rfl

/-- Exact one-step formula in the position cutoff.  The newly exposed row
contributes precisely when its permutation value lies below the value
cutoff. -/
theorem northwestRankNat_succ_left_eq
    (w : FinPermutation n) (r s : ℕ) (hr : r < n) :
    northwestRankNat w (r + 1) s =
      northwestRankNat w r s +
        if (w ⟨r, hr⟩).1 < s then 1 else 0 := by
  classical
  let k : Fin n := ⟨r, hr⟩
  let A := Finset.univ.filter
    (fun i : Fin n ↦ i.1 < r + 1 ∧ (w i).1 < s)
  let B := Finset.univ.filter
    (fun i : Fin n ↦ i.1 < r ∧ (w i).1 < s)
  have hkB : k ∉ B := by
    simp [B, k]
  by_cases hk : (w k).1 < s
  · have hset : A = insert k B := by
      ext i
      simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert]
      constructor
      · rintro ⟨hir, his⟩
        by_cases hirEq : i.1 = r
        · exact Or.inl (Fin.ext hirEq)
        · exact Or.inr ⟨by omega, his⟩
      · rintro (hik | ⟨hir, his⟩)
        · subst i
          exact ⟨by simp [k], hk⟩
        · exact ⟨by omega, his⟩
    change A.card = B.card + if (w k).1 < s then 1 else 0
    rw [if_pos hk, hset, Finset.card_insert_of_notMem hkB]
  · have hset : A = B := by
      ext i
      simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hir, his⟩
        have hirNe : i.1 ≠ r := by
          intro hirEq
          apply hk
          have hik : i = k := by
            apply Fin.ext
            simpa [k] using hirEq
          simpa [hik] using his
        exact ⟨by omega, his⟩
      · rintro ⟨hir, his⟩
        exact ⟨by omega, his⟩
    change A.card = B.card + if (w k).1 < s then 1 else 0
    rw [if_neg hk, hset, add_zero]

/-- Adding one value to a northwest rectangle increases its rank by at most
one. -/
theorem northwestRankNat_succ_right_le
    (w : FinPermutation n) (r s : ℕ) (hs : s < n) :
    northwestRankNat w r (s + 1) ≤ northwestRankNat w r s + 1 := by
  classical
  let value : Fin n := ⟨s, hs⟩
  let k : Fin n := w.symm value
  let A := Finset.univ.filter
    (fun i : Fin n ↦ i.1 < r ∧ (w i).1 < s + 1)
  let B := Finset.univ.filter
    (fun i : Fin n ↦ i.1 < r ∧ (w i).1 < s)
  have hsubset : A ⊆ insert k B := by
    intro i hi
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    by_cases his : (w i).1 = s
    · apply Finset.mem_insert.mpr
      left
      apply w.injective
      simpa [k, value] using Fin.ext his
    · exact Finset.mem_insert.mpr (Or.inr (by
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hi.1, by omega⟩))
  calc
    northwestRankNat w r (s + 1) = A.card := rfl
    _ ≤ (insert k B).card := Finset.card_le_card hsubset
    _ ≤ B.card + 1 := Finset.card_insert_le k B
    _ = northwestRankNat w r s + 1 := rfl

/-- Exact one-step formula in the value cutoff.  The newly exposed value
contributes precisely when its inverse image lies before the position
cutoff. -/
theorem northwestRankNat_succ_right_eq
    (w : FinPermutation n) (r s : ℕ) (hs : s < n) :
    northwestRankNat w r (s + 1) =
      northwestRankNat w r s +
        if ((w.symm : FinPermutation n) ⟨s, hs⟩).1 < r then 1 else 0 := by
  rw [← northwestRankNat_symm w (s + 1) r,
    ← northwestRankNat_symm w s r]
  exact northwestRankNat_succ_left_eq
    (w.symm : FinPermutation n) s r hs

/-- Moving the position cutoff from `r` to `R` can add at most `R-r`
entries. -/
theorem northwestRankNat_le_add_left
    (w : FinPermutation n) (s : ℕ) {r R : ℕ}
    (hrR : r ≤ R) (hRn : R ≤ n) :
    northwestRankNat w R s ≤ northwestRankNat w r s + (R - r) := by
  induction R, hrR using Nat.le_induction with
  | base => simp
  | succ R hrR ih =>
      have hRlt : R < n := by omega
      have hstep := northwestRankNat_succ_left_le w R s hRlt
      omega

/-- Moving the value cutoff from `s` to `S` can add at most `S-s`
entries. -/
theorem northwestRankNat_le_add_right
    (w : FinPermutation n) (r : ℕ) {s S : ℕ}
    (hsS : s ≤ S) (hSn : S ≤ n) :
    northwestRankNat w r S ≤ northwestRankNat w r s + (S - s) := by
  induction S, hsS using Nat.le_induction with
  | base => simp
  | succ S hsS ih =>
      have hSlt : S < n := by omega
      have hstep := northwestRankNat_succ_right_le w r S hSlt
      omega

/-- Simultaneously enlarging both cutoffs gives the sum of the two possible
rank increases. -/
theorem northwestRankNat_le_add
    (w : FinPermutation n) {r s R S : ℕ}
    (hrR : r ≤ R) (hsS : s ≤ S) (hRn : R ≤ n) (hSn : S ≤ n) :
    northwestRankNat w R S ≤
      northwestRankNat w r s + (R - r) + (S - s) := by
  have hright := northwestRankNat_le_add_right w R hsS hSn
  have hleft := northwestRankNat_le_add_left w s hrR hRn
  omega

/-- Relative to any fixed corner, an arbitrary northwest rank is bounded by
the corner rank plus the positive increases of the two cutoffs. -/
theorem northwestRankNat_le_corner_add
    (w : FinPermutation n) {r s R S : ℕ}
    (hrn : r ≤ n) (hsn : s ≤ n) (hRn : R ≤ n) (hSn : S ≤ n) :
    northwestRankNat w R S ≤
      northwestRankNat w r s + (R - r) + (S - s) := by
  by_cases hrR : r ≤ R
  · by_cases hsS : s ≤ S
    · exact northwestRankNat_le_add w hrR hsS hRn hSn
    · have hSR : S ≤ s := Nat.le_of_not_ge hsS
      have hmono := northwestRankNat_mono_right w R hSR
      have hleft := northwestRankNat_le_add_left w s hrR hRn
      omega
  · have hRr : R ≤ r := Nat.le_of_not_ge hrR
    by_cases hsS : s ≤ S
    · have hmono := northwestRankNat_mono_left w S hRr
      have hright := northwestRankNat_le_add_right w r hsS hSn
      omega
    · have hSs : S ≤ s := Nat.le_of_not_ge hsS
      have hmono := northwestRankNat_mono w hRr hSs
      omega

/-- A northwest rank never exceeds the number of available positions. -/
theorem northwestRankNat_le_left
    (w : FinPermutation n) {r s : ℕ} (hrn : r ≤ n) :
    northwestRankNat w r s ≤ r := by
  have h := northwestRankNat_le_add_left w s (r := 0) (R := r)
    (Nat.zero_le r) hrn
  simpa [northwestRankNat] using h

/-- A northwest rank never exceeds the number of available values. -/
theorem northwestRankNat_le_right
    (w : FinPermutation n) {r s : ℕ} (hsn : s ≤ n) :
    northwestRankNat w r s ≤ s := by
  have h := northwestRankNat_le_add_right w r (s := 0) (S := s)
    (Nat.zero_le s) hsn
  simpa [northwestRankNat] using h

end FinPermutation

end Schubert
