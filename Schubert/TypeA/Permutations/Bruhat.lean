import Schubert.TypeA.Permutations.Basic

/-! # Strong Bruhat order in rank-matrix form -/

namespace Schubert

namespace FinPermutation

variable {n : ℕ}

/-- Southwest rank number used to characterize strong Bruhat order. -/
def bruhatRank (w : FinPermutation n) (p q : Fin n) : ℕ :=
  (Finset.univ.filter fun i ↦ i ≤ p ∧ q ≤ w i).card

/-- Strong Bruhat comparison, using the rank-matrix criterion.

With this convention the identity permutation is the minimum element. -/
def StrongBruhatLE (u v : FinPermutation n) : Prop :=
  ∀ p q, u.bruhatRank p q ≤ v.bruhatRank p q

infix:50 " ≤ᴮ " => StrongBruhatLE

theorem strongBruhat_refl (w : FinPermutation n) : w ≤ᴮ w :=
  fun _ _ ↦ le_rfl

theorem strongBruhat_trans {u v w : FinPermutation n}
    (huv : u ≤ᴮ v) (hvw : v ≤ᴮ w) : u ≤ᴮ w :=
  fun p q ↦ (huv p q).trans (hvw p q)

/-- If two permutations agree before `i`, but a threshold contains the value
of only the first permutation at `i`, their rank numbers at `(i,q)` differ. -/
private theorem rank_ne_of_threshold {u v : FinPermutation n}
    (i q : Fin n) (hbefore : ∀ k, k < i → u k = v k)
    (hu : q ≤ u i) (hv : ¬ q ≤ v i) :
    u.bruhatRank i q ≠ v.bruhatRank i q := by
    let U := Finset.univ.filter fun k : Fin n ↦ k ≤ i ∧ q ≤ u k
    let V := Finset.univ.filter fun k : Fin n ↦ k ≤ i ∧ q ≤ v k
    have herase : U.erase i = V.erase i := by
      ext k
      simp only [U, V, Finset.mem_erase, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hki, hkle, hq⟩
        have hlt : k < i := lt_of_le_of_ne hkle hki
        exact ⟨hki, hkle, by simpa [hbefore k hlt] using hq⟩
      · rintro ⟨hki, hkle, hq⟩
        have hlt : k < i := lt_of_le_of_ne hkle hki
        exact ⟨hki, hkle, by simpa [hbefore k hlt] using hq⟩
    have hiU : i ∈ U := by simp [U, hu]
    have hiV : i ∉ V := by simp [V, hv]
    have hU := Finset.card_erase_add_one hiU
    have hV : V.erase i = V := Finset.erase_eq_of_notMem hiV
    have heraseCard : (U.erase i).card = (V.erase i).card :=
      congrArg Finset.card herase
    have hcards : U.card ≠ V.card := by
      intro hcard
      have himpossible : (U.erase i).card + 1 = (U.erase i).card := calc
        (U.erase i).card + 1 = U.card := hU
        _ = V.card := hcard
        _ = (V.erase i).card := by rw [hV]
        _ = (U.erase i).card := heraseCard.symm
      omega
    simpa [bruhatRank, U, V] using hcards

/-- A rank row determines the new permutation entry once all earlier entries
are known. -/
theorem eq_at_of_bruhatRank_row_eq_of_eq_before {u v : FinPermutation n}
    (i : Fin n) (hrank : ∀ q, u.bruhatRank i q = v.bruhatRank i q)
    (hbefore : ∀ k, k < i → u k = v k) :
    u i = v i := by
  apply le_antisymm
  · by_contra h
    have hlt : v i < u i := lt_of_not_ge h
    exact rank_ne_of_threshold i (u i) hbefore le_rfl
      (not_le_of_gt hlt) (hrank (u i))
  · by_contra h
    have hlt : u i < v i := lt_of_not_ge h
    have hne := rank_ne_of_threshold (u := v) (v := u) i (v i)
      (fun k hk ↦ (hbefore k hk).symm) le_rfl (not_le_of_gt hlt)
    exact hne (hrank (v i)).symm

/-- The rank-matrix comparison is antisymmetric. -/
theorem strongBruhat_antisymm {u v : FinPermutation n}
    (huv : u ≤ᴮ v) (hvu : v ≤ᴮ u) : u = v := by
  have hrank : ∀ p q, u.bruhatRank p q = v.bruhatRank p q :=
    fun p q ↦ Nat.le_antisymm (huv p q) (hvu p q)
  apply Equiv.ext
  intro i
  apply wellFounded_lt.induction i
  intro i ih
  exact eq_at_of_bruhatRank_row_eq_of_eq_before i (hrank i) ih

/-- Strong Bruhat comparison as an explicit partial-order package.  It is
kept named rather than installed globally, so it does not conflict with the
pointwise order inherited by equivalences. -/
@[reducible] def strongBruhatPartialOrder (n : ℕ) : PartialOrder (FinPermutation n) where
  le := StrongBruhatLE
  le_refl := strongBruhat_refl
  le_trans := fun _ _ _ ↦ strongBruhat_trans
  le_antisymm := fun _ _ ↦ strongBruhat_antisymm

/-- The permutations minimal in strong Bruhat order among those not below `w`.
This is the order-theoretic essential set used in the paper. -/
def bruhatEssentialSet (w : FinPermutation n) : Set (FinPermutation n) :=
  {v | ¬ v ≤ᴮ w ∧
    ∀ u, u ≤ᴮ v → u ≠ v → u ≤ᴮ w}

theorem mem_bruhatEssentialSet_iff (w v : FinPermutation n) :
    v ∈ w.bruhatEssentialSet ↔
      ¬ v ≤ᴮ w ∧ ∀ u, u ≤ᴮ v → u ≠ v → u ≤ᴮ w :=
  Iff.rfl

end FinPermutation

end Schubert
