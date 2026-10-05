import Schubert.Demazure.JosephPolo.DefiningChains
import Schubert.Demazure.JosephPolo.BruhatLifting

/-!
# Least lifts in Grassmannian cosets and right keys

For `k : Fin n` and a set `R` of `k + 1` values, the permutations `v` with
`v({0, …, k}) = R` form a coset of the Young subgroup `S_{k+1} × S_{n-k-1}` (acting on
positions). Deodhar's lifting lemma, in this Grassmannian case, states that for every
permutation `x` the coset elements above `x` in Bruhat order, if any, have a least element
(`exists_least_inPrefixCoset`).

Consequently, for a tuple `T` of row sets admitting a defining chain, the permutations `w`
for which `T` has a defining chain bounded by `w` are exactly those above a single
permutation, the right key of `T` (`exists_rightKey`). The proof builds the least chain
greedily, column by column.
-/

open Schubert

namespace Demazure.SchubertUnions

open FinPermutation FlagModule

variable {n : ℕ}

/-! ### Left multiplication by an adjacent transposition -/

theorem leftAdjacentSwap_symm_apply (w : FinPermutation n) (i : AdjacentPosition n)
    (x : Fin n) : (w.leftAdjacentSwap i).symm x = w.symm (adjacentTransposition i x) := by
  simp [leftAdjacentSwap, adjacentTransposition, Equiv.symm_swap]

theorem leftAdjacentSwap_leftAdjacentSwap (w : FinPermutation n) (i : AdjacentPosition n) :
    (w.leftAdjacentSwap i).leftAdjacentSwap i = w := by
  apply Equiv.ext
  intro j
  simp [leftAdjacentSwap, adjacentTransposition]

theorem leftAdjacentSwap_symm_left (w : FinPermutation n) (i : AdjacentPosition n) :
    (w.leftAdjacentSwap i).symm i.left = w.symm i.right := by
  rw [leftAdjacentSwap_symm_apply]
  simp [adjacentTransposition]

theorem leftAdjacentSwap_symm_right (w : FinPermutation n) (i : AdjacentPosition n) :
    (w.leftAdjacentSwap i).symm i.right = w.symm i.left := by
  rw [leftAdjacentSwap_symm_apply]
  simp [adjacentTransposition]

/-- Left lifting when both permutations have a left ascent at `i`. -/
theorem left_reflections_le_of_both_ascent (i : AdjacentPosition n) {u v : FinPermutation n}
    (h : u ≤ᴮ v) (hu : u.symm i.left < u.symm i.right) (hv : v.symm i.left < v.symm i.right) :
    u.leftAdjacentSwap i ≤ᴮ v.leftAdjacentSwap i := by
  have h1 : u ≤ᴮ v.leftAdjacentSwap i := strongBruhat_trans h (le_left_reflection_of_ascent i v hv)
  have hd : (v.leftAdjacentSwap i).symm i.right < (v.leftAdjacentSwap i).symm i.left := by
    rw [leftAdjacentSwap_symm_left, leftAdjacentSwap_symm_right]
    exact hv
  exact left_reflected_lower_le_upper i h1 hu hd

/-! ### Grassmannian cosets -/

/-- `v` sends the positions `0, …, k` onto `R`. -/
def InPrefixCoset (v : FinPermutation n) (k : Fin n) (R : Finset (Fin n)) : Prop :=
  ∀ j, v j ∈ R ↔ j ≤ k

theorem inPrefixCoset_iff_flagPrefixRows (v : FinPermutation n) (k : Fin n)
    (R : FlagMinorRowSet k) : flagPrefixRows v k = R ↔ InPrefixCoset v k R.val := by
  have hmem : ∀ j, v j ∈ (flagPrefixRows v k).val ↔ j ≤ k := by
    intro j
    change v j ∈ Finset.univ.image (fun a => v (prefixIndex k a)) ↔ j ≤ k
    rw [Finset.mem_image]
    constructor
    · rintro ⟨a, -, ha⟩
      have := v.injective ha
      rw [← this, Fin.le_def]
      simp only [prefixIndex]
      omega
    · intro hj
      refine ⟨⟨j.val, by rw [Fin.le_def] at hj; omega⟩, Finset.mem_univ _, ?_⟩
      rfl
  constructor
  · rintro rfl
    exact hmem
  · intro h
    apply Subtype.ext
    ext x
    have h1 := hmem (v.symm x)
    have h2 := h (v.symm x)
    rw [Equiv.apply_symm_apply] at h1 h2
    rw [h1, h2]

/-- Left multiplication by `sᵢ` moves the coset of `R` to the coset of `sᵢ(R)`. -/
theorem inPrefixCoset_leftAdjacentSwap_iff (v : FinPermutation n) (k : Fin n)
    (R : Finset (Fin n)) (i : AdjacentPosition n) :
    InPrefixCoset (v.leftAdjacentSwap i) k (R.map (adjacentTransposition i).toEmbedding) ↔
      InPrefixCoset v k R := by
  unfold InPrefixCoset
  refine forall_congr' fun j => ?_
  rw [leftAdjacentSwap_apply, Finset.mem_map_equiv]
  simp [adjacentTransposition]

theorem descent_of_inPrefixCoset {v : FinPermutation n} {k : Fin n} {R : Finset (Fin n)}
    (hv : InPrefixCoset v k R) {i : AdjacentPosition n} (hr : i.right ∈ R) (hl : i.left ∉ R) :
    v.symm i.right < v.symm i.left := by
  have h1 := hv (v.symm i.right)
  have h2 := hv (v.symm i.left)
  rw [Equiv.apply_symm_apply] at h1 h2
  have a := h1.mp hr
  have b : ¬ v.symm i.left ≤ k := fun h => hl (h2.mpr h)
  exact lt_of_le_of_lt a (lt_of_not_ge b)

theorem ascent_of_inPrefixCoset {v : FinPermutation n} {k : Fin n} {R : Finset (Fin n)}
    (hv : InPrefixCoset v k R) {i : AdjacentPosition n} (hl : i.left ∈ R) (hr : i.right ∉ R) :
    v.symm i.left < v.symm i.right := by
  have h1 := hv (v.symm i.left)
  have h2 := hv (v.symm i.right)
  rw [Equiv.apply_symm_apply] at h1 h2
  have a := h1.mp hl
  have b : ¬ v.symm i.right ≤ k := fun h => hr (h2.mpr h)
  exact lt_of_le_of_lt a (lt_of_not_ge b)

theorem sum_map_adjacentTransposition_lt (R : Finset (Fin n)) (i : AdjacentPosition n)
    (hr : i.right ∈ R) (hl : i.left ∉ R) :
    ∑ r ∈ R.map (adjacentTransposition i).toEmbedding, r.val < ∑ r ∈ R, r.val := by
  rw [Finset.sum_map]
  rw [← Finset.add_sum_erase R _ hr, ← Finset.add_sum_erase R (fun r : Fin n => r.val) hr]
  have hrest : ∑ x ∈ R.erase i.right, ((adjacentTransposition i).toEmbedding x).val =
      ∑ x ∈ R.erase i.right, x.val := by
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxr : x ≠ i.right := Finset.ne_of_mem_erase hx
    have hxl : x ≠ i.left := fun h => hl (h ▸ Finset.mem_of_mem_erase hx)
    simp [adjacentTransposition, Equiv.swap_apply_of_ne_of_ne hxl hxr]
  rw [hrest]
  have : ((adjacentTransposition i).toEmbedding i.right).val = i.left.val := by
    simp [adjacentTransposition]
  rw [this]
  have := i.right_val
  omega

/-- A set of values closed under predecessors, with the right size, is `{0, …, k}`. -/
theorem eq_Iic_of_closed {k : Fin n} {R : Finset (Fin n)} {v : FinPermutation n}
    (hv : InPrefixCoset v k R)
    (hclosed : ∀ i : AdjacentPosition n, i.right ∈ R → i.left ∈ R) : R = Finset.Iic k := by
  have hdown : ∀ r ∈ R, ∀ j : Fin n, j ≤ r → j ∈ R := by
    intro r hr j hj
    obtain ⟨d, hd⟩ : ∃ d, r.val = j.val + d := ⟨r.val - j.val, by rw [Fin.le_def] at hj; omega⟩
    induction d generalizing r with
    | zero => rwa [show r = j from Fin.ext (by omega)] at hr
    | succ d ih =>
      let i : AdjacentPosition n := ⟨⟨r.val - 1, by omega⟩, by simp; omega⟩
      have hir : i.right = r := Fin.ext (by rw [AdjacentPosition.right_val]; simp [i]; omega)
      have hil := hclosed i (hir ▸ hr)
      exact ih i.left hil (by rw [Fin.le_def]; simp [i]; omega) (by simp [i]; omega)
  have hcard : R.card = k.val + 1 := by
    have : R = (Finset.Iic k).map v.toEmbedding := by
      ext x
      rw [Finset.mem_map_equiv, Finset.mem_Iic, ← hv, Equiv.apply_symm_apply]
    rw [this, Finset.card_map, Fin.card_Iic]
  have hsub : R ⊆ Finset.Iic k := by
    intro r hr
    rw [Finset.mem_Iic, Fin.le_def]
    have hsub' : Finset.Iic r ⊆ R := fun j hj => hdown r hr j (Finset.mem_Iic.mp hj)
    have := Finset.card_le_card hsub'
    rw [Fin.card_Iic, hcard] at this
    omega
  exact Finset.eq_of_subset_of_card_le hsub (by rw [Fin.card_Iic, hcard])

/-- The coset of `{0, …, k}` is a lower set for Bruhat order. -/
theorem inPrefixCoset_Iic_of_le {k : Fin n} {x v : FinPermutation n}
    (hv : InPrefixCoset v k (Finset.Iic k)) (hxv : x ≤ᴮ v) : InPrefixCoset x k (Finset.Iic k) := by
  have hinto : ∀ j, j ≤ k → x j ≤ k := by
    intro j hj
    by_contra hx
    have hk1 : k.val + 1 < n := by
      have := (x j).isLt
      rw [Fin.le_def] at hx
      omega
    let q : Fin n := ⟨k.val + 1, hk1⟩
    have hrank := hxv k q
    have hv0 : v.bruhatRank k q = 0 := by
      unfold bruhatRank
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro i - ⟨hik, hqi⟩
      have := (hv i).mpr hik
      rw [Finset.mem_Iic, Fin.le_def] at this
      rw [Fin.le_def] at hqi
      simp [q] at hqi
      omega
    have hx0 : 0 < x.bruhatRank k q := by
      unfold bruhatRank
      rw [Finset.card_pos]
      refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj, ?_⟩⟩
      rw [Fin.le_def]
      rw [Fin.le_def] at hx
      simp [q]
      omega
    omega
  intro j
  rw [Finset.mem_Iic]
  constructor
  · intro hxj
    by_contra hj
    have himage : (Finset.Iic k).map x.toEmbedding = Finset.Iic k := by
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hy
        exact Finset.mem_Iic.mpr (hinto a (Finset.mem_Iic.mp ha))
      · rw [Finset.card_map]
    have : x j ∈ (Finset.Iic k).map x.toEmbedding := by rw [himage]; exact Finset.mem_Iic.mpr hxj
    obtain ⟨a, ha, hax⟩ := Finset.mem_map.mp this
    have := x.injective hax
    subst this
    exact hj (Finset.mem_Iic.mp ha)
  · exact hinto j

/-- **Deodhar's lifting lemma** for the Grassmannian coset of `R`: the coset elements above
`x`, if any, have a least element. -/
theorem exists_least_inPrefixCoset (k : Fin n) (R : Finset (Fin n)) (x : FinPermutation n)
    (hne : ∃ v, InPrefixCoset v k R ∧ x ≤ᴮ v) :
    ∃ v₀, InPrefixCoset v₀ k R ∧ x ≤ᴮ v₀ ∧ ∀ v, InPrefixCoset v k R → x ≤ᴮ v → v₀ ≤ᴮ v := by
  generalize hs : ∑ r ∈ R, r.val = s
  induction s using Nat.strong_induction_on generalizing R x with
  | h s ih =>
    obtain ⟨v, hv, hxv⟩ := hne
    by_cases hstep : ∃ i : AdjacentPosition n, i.right ∈ R ∧ i.left ∉ R
    · obtain ⟨i, hr, hl⟩ := hstep
      let R' := R.map (adjacentTransposition i).toEmbedding
      have hlt : ∑ r ∈ R', r.val < s := hs ▸ sum_map_adjacentTransposition_lt R i hr hl
      have hR' : ∀ w, InPrefixCoset w k R → InPrefixCoset (w.leftAdjacentSwap i) k R' :=
        fun w hw => (inPrefixCoset_leftAdjacentSwap_iff w k R i).mpr hw
      have hR'back : ∀ w', InPrefixCoset w' k R' → InPrefixCoset (w'.leftAdjacentSwap i) k R := by
        intro w' hw'
        rw [← inPrefixCoset_leftAdjacentSwap_iff _ k R i, leftAdjacentSwap_leftAdjacentSwap]
        exact hw'
      have hl' : i.left ∈ R' := by
        rw [Finset.mem_map_equiv]
        simpa [adjacentTransposition] using hr
      have hr' : i.right ∉ R' := by
        rw [Finset.mem_map_equiv]
        simpa [adjacentTransposition] using hl
      have hdesc : ∀ w, InPrefixCoset w k R → w.symm i.right < w.symm i.left :=
        fun w hw => descent_of_inPrefixCoset hw hr hl
      have hasc : ∀ w', InPrefixCoset w' k R' → w'.symm i.left < w'.symm i.right :=
        fun w' hw' => ascent_of_inPrefixCoset hw' hl' hr'
      rcases lt_or_gt_of_ne (fun h => i.left_ne_right (x.symm.injective h) :
          x.symm i.left ≠ x.symm i.right) with hxa | hxd
      · -- `x` has a left ascent at `i`
        obtain ⟨v₀', hv₀', hxv₀', hleast⟩ := ih _ hlt R' x
          ⟨v.leftAdjacentSwap i, hR' v hv, left_lower_le_reflected_upper i hxv hxa (hdesc v hv)⟩ rfl
        refine ⟨v₀'.leftAdjacentSwap i, hR'back v₀' hv₀',
          strongBruhat_trans hxv₀' (le_left_reflection_of_ascent i v₀' (hasc v₀' hv₀')),
          fun w hw hxw => ?_⟩
        have h1 := hleast (w.leftAdjacentSwap i) (hR' w hw)
          (left_lower_le_reflected_upper i hxw hxa (hdesc w hw))
        have h2 := left_reflections_le_of_both_ascent i h1 (hasc v₀' hv₀')
          (hasc _ (hR' w hw))
        rwa [leftAdjacentSwap_leftAdjacentSwap] at h2
      · -- `x` has a left descent at `i`
        have hx'a : (x.leftAdjacentSwap i).symm i.left < (x.leftAdjacentSwap i).symm i.right := by
          rw [leftAdjacentSwap_symm_left, leftAdjacentSwap_symm_right]; exact hxd
        obtain ⟨v₀', hv₀', hxv₀', hleast⟩ := ih _ hlt R' (x.leftAdjacentSwap i)
          ⟨v.leftAdjacentSwap i, hR' v hv,
            left_reflections_le_of_both_descent i hxv hxd (hdesc v hv)⟩ rfl
        refine ⟨v₀'.leftAdjacentSwap i, hR'back v₀' hv₀', ?_, fun w hw hxw => ?_⟩
        · have h := left_reflections_le_of_both_ascent i hxv₀' hx'a (hasc v₀' hv₀')
          rwa [leftAdjacentSwap_leftAdjacentSwap] at h
        · have h1 := hleast (w.leftAdjacentSwap i) (hR' w hw)
            (left_reflections_le_of_both_descent i hxw hxd (hdesc w hw))
          have h2 := left_reflections_le_of_both_ascent i h1 (hasc v₀' hv₀')
            (hasc _ (hR' w hw))
          rwa [leftAdjacentSwap_leftAdjacentSwap] at h2
    · -- base case: `R = {0, …, k}` and `x` lies in the coset
      have hclosed : ∀ i : AdjacentPosition n, i.right ∈ R → i.left ∈ R := by
        intro i hr
        by_contra hl
        exact hstep ⟨i, hr, hl⟩
      have hR := eq_Iic_of_closed hv hclosed
      subst hR
      exact ⟨x, inPrefixCoset_Iic_of_le hv hxv, strongBruhat_refl x, fun w _ hxw => hxw⟩

/-- **Right keys.** If a tuple of row sets has a defining chain, then there is a permutation `κ`
such that the tuple has a defining chain bounded by `w` exactly when `κ ≤ w`. -/
theorem exists_rightKey {d : ℕ} (h : Fin d → Fin n) (T : (j : Fin d) → FlagMinorRowSet (h j))
    (hT : ∃ w, HasFlagDefiningChain h T w) :
    ∃ κ : FinPermutation n, ∀ w, HasFlagDefiningChain h T w ↔ κ ≤ᴮ w := by
  induction d with
  | zero =>
    refine ⟨Equiv.refl _, fun w => ⟨fun _ => refl_strongBruhatLE w, fun _ => ?_⟩⟩
    exact ⟨fun j => j.elim0, fun i => i.elim0, fun j => j.elim0, fun j => j.elim0⟩
  | succ d ih =>
    obtain ⟨w₀, hw₀⟩ := hT
    obtain ⟨v₁, -, -, hchain₁⟩ := hasFlagDefiningChain_iff_last.mp hw₀
    obtain ⟨κ', hκ'⟩ := ih (fun j => h j.castSucc) (fun j => T j.castSucc) ⟨v₁, hchain₁⟩
    obtain ⟨v₀, hv₀, hκv₀, hleast⟩ := exists_least_inPrefixCoset (h (Fin.last d))
      (T (Fin.last d)).val κ' (by
        obtain ⟨v, -, hv, hc⟩ := hasFlagDefiningChain_iff_last.mp hw₀
        exact ⟨v, (inPrefixCoset_iff_flagPrefixRows _ _ _).mp hv, (hκ' v).mp hc⟩)
    refine ⟨v₀, fun w => ⟨fun hw => ?_, fun hle => ?_⟩⟩
    · obtain ⟨v, hvw, hv, hc⟩ := hasFlagDefiningChain_iff_last.mp hw
      exact strongBruhat_trans (hleast v ((inPrefixCoset_iff_flagPrefixRows _ _ _).mp hv)
        ((hκ' v).mp hc)) hvw
    · exact hasFlagDefiningChain_iff_last.mpr
        ⟨v₀, hle, (inPrefixCoset_iff_flagPrefixRows _ _ _).mpr hv₀, (hκ' v₀).mpr hκv₀⟩

end Demazure.SchubertUnions
