import Schubert.RS.JosephPolo.PrefixMinors
import Schubert.RS.JosephPolo.BruhatLifting

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation

def FlagMinorRowSet.permute {n : ℕ} {k : Fin n} (S : FlagMinorRowSet k)
    (w : FinPermutation n) : FlagMinorRowSet k :=
  ⟨S.val.map w.toEmbedding,by
    apply Finset.mem_powersetCard.mpr
    exact ⟨Finset.subset_univ _,by
      rw [Finset.card_map]
      exact (Finset.mem_powersetCard.mp S.property).2⟩⟩

theorem FlagMinorRowSet.mem_permute {n : ℕ} {k : Fin n} (S : FlagMinorRowSet k)
    (w : FinPermutation n) (a : Fin n) :
    a ∈ (S.permute w).val ↔ w.symm a ∈ S.val := by
  classical
  simp [FlagMinorRowSet.permute]

theorem mem_flagPrefixRows {n : ℕ} (w : FinPermutation n) (k a : Fin n) :
    a ∈ (flagPrefixRows w k).val ↔ w.symm a ≤ k := by
  classical
  change a ∈ Finset.univ.image (fun j => w (prefixIndex k j)) ↔ _
  constructor
  · intro ha
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp ha
    rw [← he,Equiv.symm_apply_apply]
    exact Nat.le_of_lt_succ j.isLt
  · intro ha
    let j : Fin (k.val+1) := ⟨(w.symm a).val,Nat.lt_succ_of_le ha⟩
    refine Finset.mem_image.mpr ⟨j,Finset.mem_univ _,?_⟩
    have hj : prefixIndex k j = w.symm a := Fin.ext rfl
    rw [hj,Equiv.apply_symm_apply]

theorem flagPrefixRows_mul {n : ℕ} (v w : FinPermutation n) (k : Fin n) :
    flagPrefixRows (v*w) k = (flagPrefixRows w k).permute v := by
  classical
  apply Subtype.ext
  ext a
  simp only [FlagMinorRowSet.mem_permute,mem_flagPrefixRows]
  rfl

theorem FlagMinorRowSet.permute_swap_eq_self {n : ℕ} {k : Fin n} (S : FlagMinorRowSet k)
    (a b : Fin n) (h : a ∈ S.val ↔ b ∈ S.val) : S.permute (Equiv.swap a b) = S := by
  classical
  apply Subtype.ext
  ext c
  rw [FlagMinorRowSet.mem_permute]
  by_cases hca : c = a
  · subst c
    simpa only [Equiv.symm_swap,Equiv.swap_apply_left] using h.symm
  · by_cases hcb : c = b
    · subst c
      simpa only [Equiv.symm_swap,Equiv.swap_apply_right] using h
    · simp only [Equiv.symm_swap,Equiv.swap_apply_of_ne_of_ne hca hcb]

theorem flagPrefixRows_mem_of_inverse_le {n : ℕ} (w : FinPermutation n) (k a b : Fin n)
    (h : w.symm a ≤ w.symm b) (hb : b ∈ (flagPrefixRows w k).val) :
    a ∈ (flagPrefixRows w k).val := by
  rw [mem_flagPrefixRows] at hb ⊢
  exact h.trans hb

theorem leftAdjacentSwap_inverse_left {n : ℕ} (w : FinPermutation n) (i : AdjacentPosition n) :
    (w.leftAdjacentSwap i).symm i.left = w.symm i.right := by
  simp [leftAdjacentSwap,adjacentTransposition]

theorem leftAdjacentSwap_inverse_right {n : ℕ} (w : FinPermutation n) (i : AdjacentPosition n) :
    (w.leftAdjacentSwap i).symm i.right = w.symm i.left := by
  simp [leftAdjacentSwap,adjacentTransposition]

/-- One-column lifting upwards inside a Bruhat interval. The implication
on membership allows a fixed column as well as a strictly raised column. -/
theorem flagColumn_lift_up {n : ℕ} (i : AdjacentPosition n) (k : Fin n)
    {v w : FinPermutation n} (hvw : v ≤ᴮ w)
    (hw : w.symm i.right < w.symm i.left)
    (hcol : i.right ∈ (flagPrefixRows v k).val → i.left ∈ (flagPrefixRows v k).val) :
    ∃ v' : FinPermutation n, v ≤ᴮ v' ∧ v' ≤ᴮ w ∧
      flagPrefixRows v' k = (flagPrefixRows v k).permute (Equiv.swap i.left i.right) ∧
      v'.symm i.right < v'.symm i.left := by
  rcases lt_or_gt_of_ne (v.symm.injective.ne i.left_ne_right) with ha | hd
  · refine ⟨v.leftAdjacentSwap i,le_left_reflection_of_ascent i v ha,
      left_reflected_lower_le_upper i hvw ha hw,?_,?_⟩
    · exact flagPrefixRows_mul (Equiv.swap i.left i.right) v k
    · rwa [leftAdjacentSwap_inverse_right,leftAdjacentSwap_inverse_left]
  · refine ⟨v,strongBruhat_refl v,hvw,?_,hd⟩
    exact (FlagMinorRowSet.permute_swap_eq_self _ _ _
      ⟨flagPrefixRows_mem_of_inverse_le v k i.right i.left hd.le,hcol⟩).symm

/-- The dual one-column lifting downwards inside a Bruhat interval. -/
theorem flagColumn_lift_down {n : ℕ} (i : AdjacentPosition n) (k : Fin n)
    {u v : FinPermutation n} (huv : u ≤ᴮ v)
    (hu : u.symm i.left < u.symm i.right)
    (hcol : i.left ∈ (flagPrefixRows v k).val → i.right ∈ (flagPrefixRows v k).val) :
    ∃ v' : FinPermutation n, u ≤ᴮ v' ∧ v' ≤ᴮ v ∧
      flagPrefixRows v' k = (flagPrefixRows v k).permute (Equiv.swap i.left i.right) ∧
      v'.symm i.left < v'.symm i.right := by
  rcases lt_or_gt_of_ne (v.symm.injective.ne i.left_ne_right) with ha | hd
  · refine ⟨v,huv,strongBruhat_refl v,?_,ha⟩
    exact (FlagMinorRowSet.permute_swap_eq_self _ _ _
      ⟨hcol,flagPrefixRows_mem_of_inverse_le v k i.left i.right ha.le⟩).symm
  · refine ⟨v.leftAdjacentSwap i,left_lower_le_reflected_upper i huv hu hd,
      left_reflection_le_of_descent i v hd,?_,?_⟩
    · exact flagPrefixRows_mul (Equiv.swap i.left i.right) v k
    · rwa [leftAdjacentSwap_inverse_left,leftAdjacentSwap_inverse_right]

end
end Schubert.RS.Representation
