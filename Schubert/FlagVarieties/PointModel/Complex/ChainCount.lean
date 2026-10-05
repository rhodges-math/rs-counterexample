import Schubert.FlagVarieties.PointModel.Complex.MinorEval

/-!
# Prefixes in Bruhat order and the chain count of the hyperplane-section identity

For a permutation `v` and a height `k`, `flagPrefixRows v k` is the set `v{0, …, k}`.

* `bruhatRank_eq_card_filter`: the rank number `r_v(k, q)` counts the elements `≥ q` of this set,
  so `v ≤ w` compares these counts (the Gale order of prefixes).
* `flagPrefixRows_eq_of_le_of_le`: prefixes are squeezed: if `u ≤ v ≤ w` and `u`, `w` have the same
  prefix, so does `v`.
* `hyperplaneSectionSet k w = {v ≤ w | v{0..k} ≠ w{0..k}}` is a Bruhat ideal not containing `w`.
* `card_chainSet_lowerSet` (**the chain count of the hyperplane-section identity**): with a
  height-`k` column placed last,
  `#chainSet h (↓w) = #chainSet h' (↓w) + #chainSet h (hyperplaneSectionSet k w)`, where `h'` drops
  the last column. The proof is a bijection on the chains of `chainSet`.
-/

open Schubert Demazure.FlagModule Demazure.SchubertUnions FinPermutation

namespace FlagVarieties.PointModel.Complex

noncomputable section

variable {n : ℕ}

/-! ### Rank numbers and prefixes -/

theorem _root_.FlagVarieties.PointModel.bruhatRank_eq_card_filter (v : Equiv.Perm (Fin n))
    (k q : Fin n) :
    bruhatRank v k q = ((flagPrefixRows v k).val.filter fun x => q ≤ x).card := by
  classical
  have himg : (flagPrefixRows v k).val.filter (fun x => q ≤ x) =
      (Finset.univ.filter fun i : Fin n => i ≤ k ∧ q ≤ v i).image v := by
    ext x
    simp only [flagPrefixRows, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨j, rfl⟩, hq⟩
      refine ⟨prefixIndex k j, ⟨?_, hq⟩, rfl⟩
      change (prefixIndex k j).val ≤ k.val
      simp only [prefixIndex]
      omega
    · rintro ⟨i, ⟨hik, hq⟩, rfl⟩
      exact ⟨⟨⟨i.val, by have : i.val ≤ k.val := hik; omega⟩, rfl⟩, hq⟩
  rw [himg, Finset.card_image_of_injective _ v.injective]
  rfl

/-- Counts of the elements `≥ q` determine a finite set of `Fin n`. -/
theorem finset_eq_of_card_filter_eq {S T : Finset (Fin n)}
    (h : ∀ q : Fin n, (S.filter fun x => q ≤ x).card = (T.filter fun x => q ≤ x).card) : S = T := by
  classical
  have key : ∀ (U : Finset (Fin n)) (x : Fin n),
      (U.filter fun y => x ≤ y).card =
        (if x ∈ U then 1 else 0) + (U.filter fun y => x < y).card := by
    intro U x
    have hsplit : U.filter (fun y => x ≤ y) =
        (U.filter fun y => y = x) ∪ U.filter fun y => x < y := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hy, hxy⟩
        rcases hxy.lt_or_eq with hlt | heq
        · exact Or.inr ⟨hy, hlt⟩
        · exact Or.inl ⟨hy, heq.symm⟩
      · rintro (⟨hy, rfl⟩ | ⟨hy, hlt⟩)
        · exact ⟨hy, le_rfl⟩
        · exact ⟨hy, hlt.le⟩
    rw [hsplit, Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun y _ hy hlt => by
      rw [hy] at hlt
      exact lt_irrefl _ hlt), Finset.filter_eq']
    by_cases hx : x ∈ U <;> simp [hx]
  have hgt : ∀ (U : Finset (Fin n)) (x : Fin n),
      (U.filter fun y => x < y).card =
        if hx : x.val + 1 < n then (U.filter fun y => (⟨x.val + 1, hx⟩ : Fin n) ≤ y).card
        else 0 := by
    intro U x
    split_ifs with hx
    · rfl
    · rw [Finset.card_eq_zero]
      ext y
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro _ hxy
      have := y.isLt
      have : x.val < y.val := hxy
      omega
  ext x
  have hx := h x
  rw [key S x, key T x, hgt S x, hgt T x] at hx
  have hrest : (if hx : x.val + 1 < n then
        (S.filter fun y => (⟨x.val + 1, hx⟩ : Fin n) ≤ y).card else 0) =
      (if hx : x.val + 1 < n then
        (T.filter fun y => (⟨x.val + 1, hx⟩ : Fin n) ≤ y).card else 0) := by
    by_cases h' : x.val + 1 < n
    · rw [dite_eq_left h', dite_eq_left h']
      exact h _
    · rw [dite_eq_right h', dite_eq_right h']
  rw [hrest, Nat.add_right_cancel_iff] at hx
  by_cases hS : x ∈ S <;> by_cases hT : x ∈ T <;> simp [hS, hT] at hx ⊢

theorem flagPrefixRows_eq_iff_bruhatRank {v w : Equiv.Perm (Fin n)} {k : Fin n} :
    flagPrefixRows v k = flagPrefixRows w k ↔ ∀ q, bruhatRank v k q = bruhatRank w k q := by
  constructor
  · intro h q
    rw [bruhatRank_eq_card_filter, bruhatRank_eq_card_filter, h]
  · intro h
    apply Subtype.ext
    apply finset_eq_of_card_filter_eq
    intro q
    rw [← bruhatRank_eq_card_filter, ← bruhatRank_eq_card_filter, h]

/-- **Squeezing of prefixes.** -/
theorem flagPrefixRows_eq_of_le_of_le {u v w : Equiv.Perm (Fin n)} {k : Fin n} (huv : u ≤ᴮ v)
    (hvw : v ≤ᴮ w) (huw : flagPrefixRows u k = flagPrefixRows w k) :
    flagPrefixRows v k = flagPrefixRows w k := by
  rw [flagPrefixRows_eq_iff_bruhatRank] at huw ⊢
  intro q
  have h1 := huv k q
  have h2 := hvw k q
  have h3 := huw q
  omega

/-- If the sorted rows of `S` are coordinatewise at most those of `T`, then `S` has at most as
many elements `≥ q` as `T`, for every `q`. -/
theorem _root_.FlagVarieties.PointModel.card_filter_le_of_rows_le {k : Fin n}
    {S T : FlagMinorRowSet k}
    (h : ∀ i, S.rows i ≤ T.rows i) (q : Fin n) :
    (S.val.filter fun x => q ≤ x).card ≤ (T.val.filter fun x => q ≤ x).card := by
  classical
  have hS : S.val.filter (fun x => q ≤ x) =
      (Finset.univ.filter fun i => q ≤ S.rows i).image S.rows := by
    conv_lhs => rw [← Finset.image_orderEmbOfFin_univ S.val
      (Finset.mem_powersetCard.mp S.property).2]
    rw [Finset.filter_image]
    rfl
  have hT : T.val.filter (fun x => q ≤ x) =
      (Finset.univ.filter fun i => q ≤ T.rows i).image T.rows := by
    conv_lhs => rw [← Finset.image_orderEmbOfFin_univ T.val
      (Finset.mem_powersetCard.mp T.property).2]
    rw [Finset.filter_image]
    rfl
  rw [hS, hT, Finset.card_image_of_injective _ S.rows.injective,
    Finset.card_image_of_injective _ T.rows.injective]
  exact Finset.card_le_card fun i hi => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi.trans (h i)

/-- For `v ≤ w` with a different prefix, the sorted prefix of `w` is not coordinatewise below that
of `v`. -/
theorem _root_.FlagVarieties.PointModel.not_rows_le_of_le_of_ne {v w : Equiv.Perm (Fin n)}
    {k : Fin n} (hvw : v ≤ᴮ w)
    (hne : flagPrefixRows v k ≠ flagPrefixRows w k) :
    ¬ ∀ i, (flagPrefixRows w k).rows i ≤ (flagPrefixRows v k).rows i := by
  intro hle
  apply hne
  rw [flagPrefixRows_eq_iff_bruhatRank]
  intro q
  have h1 := hvw k q
  have h2 := card_filter_le_of_rows_le hle q
  rw [← bruhatRank_eq_card_filter, ← bruhatRank_eq_card_filter] at h2
  omega

/-! ### Bruhat intervals and the hyperplane set -/

theorem _root_.FlagVarieties.PointModel.bruhatLower_lowerSet (w : Equiv.Perm (Fin n)) :
    BruhatLower (lowerSet w) := by
  intro u hu v hv
  rw [mem_lowerSet] at hu ⊢
  exact strongBruhat_trans hv hu

theorem _root_.FlagVarieties.PointModel.mem_lowerSet_self (w : Equiv.Perm (Fin n)) :
    w ∈ lowerSet w :=
  mem_lowerSet.mpr (strongBruhat_refl w)

export PointModel (bruhatLower_lowerSet)

/-- `D_k(w) = {v ≤ w | v{0..k} ≠ w{0..k}}`: the part of `X_w` where the flag minor
`Δ_{w{0..k}}` vanishes. -/
def _root_.FlagVarieties.PointModel.hyperplaneSectionSet (k : Fin n) (w : Equiv.Perm (Fin n)) :
    Finset (Equiv.Perm (Fin n)) :=
  (lowerSet w).filter fun v => flagPrefixRows v k ≠ flagPrefixRows w k

theorem _root_.FlagVarieties.PointModel.mem_hyperplaneSectionSet {k : Fin n}
    {v w : Equiv.Perm (Fin n)} :
    v ∈ hyperplaneSectionSet k w ↔ v ≤ᴮ w ∧ flagPrefixRows v k ≠ flagPrefixRows w k := by
  rw [hyperplaneSectionSet, Finset.mem_filter, mem_lowerSet]

theorem _root_.FlagVarieties.PointModel.hyperplaneSectionSet_subset (k : Fin n)
    (w : Equiv.Perm (Fin n)) : hyperplaneSectionSet k w ⊆ lowerSet w :=
  Finset.filter_subset _ _

theorem _root_.FlagVarieties.PointModel.self_notMem_hyperplaneSectionSet (k : Fin n)
    (w : Equiv.Perm (Fin n)) : w ∉ hyperplaneSectionSet k w := by
  rw [mem_hyperplaneSectionSet]
  exact fun h => h.2 rfl

theorem card_hyperplaneSectionSet_lt (k : Fin n) (w : Equiv.Perm (Fin n)) :
    (hyperplaneSectionSet k w).card < (lowerSet w).card :=
  Finset.card_lt_card ((Finset.ssubset_iff_of_subset (hyperplaneSectionSet_subset k w)).mpr
    ⟨w, mem_lowerSet_self w, self_notMem_hyperplaneSectionSet k w⟩)

theorem _root_.FlagVarieties.PointModel.bruhatLower_hyperplaneSectionSet (k : Fin n)
    (w : Equiv.Perm (Fin n)) : BruhatLower (hyperplaneSectionSet k w) := by
  intro v hv u huv
  rw [mem_hyperplaneSectionSet] at hv ⊢
  refine ⟨strongBruhat_trans huv hv.1, fun h => hv.2 ?_⟩
  exact flagPrefixRows_eq_of_le_of_le huv hv.1 h

/-! ### The chain count -/

theorem mem_chainSet_lowerSet {d : ℕ} {h : Fin d → Fin n} {w : Equiv.Perm (Fin n)}
    {T : (j : Fin d) → FlagMinorRowSet (h j)} :
    T ∈ chainSet h (lowerSet w) ↔ HasFlagDefiningChain h T w := by
  rw [mem_chainSet]
  constructor
  · rintro ⟨v, hv, hc⟩
    exact hc.mono (mem_lowerSet.mp hv)
  · intro hc
    exact ⟨w, mem_lowerSet_self w, hc⟩

/-- **The chain count of the hyperplane-section identity.** -/
theorem _root_.FlagVarieties.PointModel.card_chainSet_lowerSet {d : ℕ} (h : Fin (d + 1) → Fin n)
    (w : Equiv.Perm (Fin n)) :
    (chainSet h (lowerSet w)).card =
      (chainSet (fun j => h j.castSucc) (lowerSet w)).card +
        (chainSet h (hyperplaneSectionSet (h (Fin.last d)) w)).card := by
  classical
  set k := h (Fin.last d) with hk
  set P := flagPrefixRows w k
  rw [← Finset.card_filter_add_card_filter_not (fun T => T (Fin.last d) = P)]
  congr 1
  · -- tuples ending with the prefix of `w` ↔ tuples of the first `d` columns
    refine Finset.card_bij' (fun T _ => fun j => T j.castSucc)
      (fun T' _ => Fin.lastCases (motive := fun j => FlagMinorRowSet (h j)) P T') ?_ ?_ ?_ ?_
    · intro T hT
      rw [Finset.mem_filter, mem_chainSet_lowerSet] at hT
      obtain ⟨v, hvw, -, hc⟩ := hT.1.last
      exact mem_chainSet_lowerSet.mpr (hc.mono hvw)
    · intro T' hT'
      rw [Finset.mem_filter, mem_chainSet_lowerSet]
      refine ⟨hasFlagDefiningChain_iff_last.mpr ⟨w, strongBruhat_refl w, ?_, ?_⟩, ?_⟩
      · rw [Fin.lastCases_last]
      · simpa only [Fin.lastCases_castSucc] using mem_chainSet_lowerSet.mp hT'
      · rw [Fin.lastCases_last]
    · intro T hT
      rw [Finset.mem_filter] at hT
      funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · rw [Fin.lastCases_last, hT.2]
      · rw [Fin.lastCases_castSucc]
    · intro T' _
      funext j
      rw [Fin.lastCases_castSucc]
  · -- tuples ending elsewhere ↔ tuples with a chain below `hyperplaneSectionSet k w`
    congr 1
    ext T
    rw [Finset.mem_filter, mem_chainSet_lowerSet, mem_chainSet]
    constructor
    · rintro ⟨hc, hne⟩
      obtain ⟨v, hvw, hp, hc'⟩ := hc.last
      refine ⟨v, mem_hyperplaneSectionSet.mpr ⟨hvw, fun hv => hne (hp.symm.trans hv)⟩, ?_⟩
      exact hasFlagDefiningChain_iff_last.mpr ⟨v, strongBruhat_refl v, hp, hc'⟩
    · rintro ⟨v, hv, hc⟩
      rw [mem_hyperplaneSectionSet] at hv
      refine ⟨hc.mono hv.1, fun hlast => ?_⟩
      obtain ⟨v', hv'v, hp, -⟩ := hc.last
      exact hv.2 (flagPrefixRows_eq_of_le_of_le hv'v hv.1 (hp.trans hlast))

end

end FlagVarieties.PointModel.Complex
