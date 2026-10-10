import RSCounterexample.Demazure.SchubertUnions.Character
import RSCounterexample.Demazure.SchubertUnions.BruhatRefinement
import RSCounterexample.Demazure.FullWeightSupport
import RSCounterexample.Demazure.PrefixOrder
import RSCounterexample.Demazure.PBW.Theorem

/-!
# The Demazure module modulo its Schubert boundary has an atom as character

Fix an ordered column sequence `h`, the shape `m = columnMultiplicity h` and `λ = shapeWeight m`.
For a permutation `σ`, the boundary `∂σ = {τ | τ < σ}` is a Bruhat ideal, so the character of
`D_{∂σ} = Σ_{τ < σ} D_τ` is the generating function of `chainSet h ∂σ`. Grouping tuples by their
right key and using the Bruhat refinement (`BruhatRefinement`), we obtain for `σ ∈ W^λ`

  `ch D_{∂σ} = κ_{σλ} − 𝒜_{σλ}`       (`chainCharacter_boundary`),

so `ch (D_σ / D_{∂σ}) = 𝒜_{σλ}`. Moreover the extremal weight `σλ` does not occur in `D_{∂σ}`
(`demazureUnion_boundary_inf_extremal`); this is the algebraic content of van der Kallen's
Remark 2.3.5.
-/

open Schubert

namespace Demazure.SchubertUnions

open FlagModule Filtrations BModules FinPermutation Schubert

noncomputable section

variable {n d : ℕ}

/-! ### Shortest coset representatives -/

/-- The sorting permutation of `σ · λ` is `σ` itself, for `σ ∈ W^λ`. -/
theorem compositionPermutation_permAct {dom : Composition n} (hdom : Antitone dom)
    {σ : FinPermutation n} (hσ : IsMinCosetRep dom σ) :
    compositionPermutation (permAct σ dom) = σ := by
  let f : Fin n → ℕᵒᵈ := fun i => OrderDual.toDual (permAct σ dom i)
  have hmono : Monotone (f ∘ σ) := by
    intro i j hij
    simp only [f, Function.comp_apply, OrderDual.toDual_le_toDual, permAct,
      Equiv.symm_apply_apply]
    exact hdom hij
  have hties : ∀ i j, i < j → f (σ i) = f (σ j) → σ i < σ j := by
    intro i j hij he
    simp only [f, OrderDual.toDual_inj, permAct, Equiv.symm_apply_apply] at he
    exact hσ i j hij he
  exact ((Tuple.eq_sort_iff (σ := σ) (f := f)).mpr ⟨hmono, hties⟩).symm

/-- The element of `W^λ` is below every element of its coset. -/
theorem le_of_extremalWeight_eq (m : ColumnShape n) {σ : FinPermutation n}
    (hσ : IsMinCosetRep (shapeWeight m) σ) (τ : FinPermutation n)
    (hτ : extremalWeight m τ = extremalWeight m σ) : σ ≤ᴮ τ := by
  generalize hl : τ.length = l
  induction l using Nat.strong_induction_on generalizing τ with
  | h l ih =>
    by_cases hτW : IsMinCosetRep (shapeWeight m) τ
    · have h1 := compositionPermutation_permAct (shapeWeight_antitone m) hτW
      have h2 := compositionPermutation_permAct (shapeWeight_antitone m) hσ
      rw [← extremalWeight_eq_permAct, hτ, extremalWeight_eq_permAct, h2] at h1
      rw [h1]
      exact strongBruhat_refl τ
    · obtain ⟨τ', ⟨hle, hne⟩, hw⟩ := exists_lt_extremalWeight_eq m τ hτW
      have hlen : τ'.length < l := by
        rw [← hl]
        exact lt_of_le_of_ne (length_le_of_strongBruhatLE hle)
          fun he => hne (eq_of_strongBruhatLE_of_length_eq hle he)
      exact strongBruhat_trans (ih _ hlen τ' (hw.trans hτ) rfl) hle

/-! ### Bruhat order and dominance of extremal weights -/

theorem lt_iff_lt_card_filter {dom : Composition n} (hdom : Antitone dom) (t : ℕ) (p : Fin n) :
    t < dom p ↔ p.val < (Finset.univ.filter fun q : Fin n => t < dom q).card := by
  constructor
  · intro hp
    have hsub : Finset.Iic p ⊆ Finset.univ.filter fun q : Fin n => t < dom q := by
      intro q hq
      rw [Finset.mem_Iic] at hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_lt_of_le hp (hdom hq)⟩
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro hp
    by_contra hn
    have hsub : (Finset.univ.filter fun q : Fin n => t < dom q) ⊆ Finset.Iio p := by
      intro q hq
      rw [Finset.mem_Iio]
      by_contra hqp
      exact hn (lt_of_lt_of_le (Finset.mem_filter.mp hq).2 (hdom (not_lt.mp hqp)))
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

theorem prefixWeight_permAct {dom : Composition n} (hdom : Antitone dom) (w : FinPermutation n)
    (k : Fin (n + 1)) :
    prefixWeight (fun i => (permAct w dom i : ℤ)) k =
      ∑ t ∈ Finset.range (Finset.univ.sup dom),
        (northwestRankNat (w.symm : FinPermutation n) k.val
          (Finset.univ.filter fun q : Fin n => t < dom q).card : ℤ) := by
  classical
  have hlayer : ∀ p : Fin n, (dom p : ℤ) =
      ∑ t ∈ Finset.range (Finset.univ.sup dom), if t < dom p then (1 : ℤ) else 0 := by
    intro p
    rw [Finset.sum_boole]
    have hp : dom p ≤ Finset.univ.sup dom := Finset.le_sup (Finset.mem_univ p)
    have : (Finset.range (Finset.univ.sup dom)).filter (fun t => t < dom p) =
        Finset.range (dom p) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [this, Finset.card_range]
  unfold prefixWeight
  simp only [permAct]
  rw [Finset.sum_congr rfl fun j _ => hlayer (w.symm j), Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  unfold northwestRankNat
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [lt_iff_lt_card_filter hdom]

/-- Bruhat order reverses dominance of extremal weights: `τ ≤ σ` implies that `σλ` is below
`τλ` in prefix order. -/
theorem prefixLE_permAct_of_le {dom : Composition n} (hdom : Antitone dom)
    {τ σ : FinPermutation n} (h : τ ≤ᴮ σ) :
    PrefixLE (fun i => (permAct σ dom i : ℤ)) (fun i => (permAct τ dom i : ℤ)) := by
  intro k
  rw [prefixWeight_permAct hdom, prefixWeight_permAct hdom]
  refine Finset.sum_le_sum fun t _ => ?_
  have hsymm : (τ.symm : FinPermutation n) ≤ᴮ (σ.symm : FinPermutation n) :=
    (strongBruhatLE_symm_iff τ σ).mpr h
  have hk : k.val ≤ n := Nat.lt_succ_iff.mp k.isLt
  have hL : (Finset.univ.filter fun q : Fin n => t < dom q).card ≤ n := by
    simpa using Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun q => t < dom q)
  exact_mod_cast (strongBruhatLE_iff_northwestRankNat_all _ _).mp hsymm k.val _ hk hL

/-! ### Weights of a single Demazure module -/

theorem finrank_flagDemazure_inf_eq_coeff (m : ColumnShape n) (τ : FinPermutation n)
    (μ : Weight n) :
    (Module.finrank ℂ (flagDemazure m τ ⊓ ambientWeight μ : Submodule ℂ (MatrixPolynomial n)) : ℤ) =
      (toLaurent (key (extremalWeight m τ))).coeff μ := by
  have hw : torusWeightSpace (flagTorus m τ) μ =
      (ambientWeight μ).comap (flagDemazure m τ).subtype := by
    ext x
    exact ⟨fun hx t => congrArg Subtype.val (hx t), fun hx t => Subtype.ext (hx t)⟩
  have hc := flagDemazure_hasTorusCharacter m τ μ
  rwa [hw, finrank_comap_subtype] at hc

/-- The weights of `D_τ` lie above `τλ` in prefix order (support in the positive root cone). -/
theorem prefixLE_of_flagDemazure_inf_ne_bot (m : ColumnShape n) (τ : FinPermutation n)
    (μ : Weight n) (hμ : flagDemazure m τ ⊓ ambientWeight μ ≠ ⊥) :
    PrefixLE (fun i => (extremalWeight m τ i : ℤ)) μ := by
  set u := extremalWeight m τ
  have hne : (toLaurent (key u)).coeff μ ≠ 0 := by
    rw [← finrank_flagDemazure_inf_eq_coeff]
    exact_mod_cast Submodule.finrank_eq_zero.not.mpr hμ
  obtain ⟨d, hd⟩ := key_support_positive_root_cone u (compositionFlagTorus u)
    (compositionFlagGenerator u) (compositionFlagJosephPolo u)
    (compositionFlagDemazureCharacter u) (orderedPBWBasis_exists n) μ hne
  rw [← hd]
  exact prefixLE_add_rootWeight _ d

/-- For `σ ∈ W^λ` and `τ < σ`, the extremal weight `σλ` is not a weight of `D_τ`. -/
theorem flagDemazure_inf_extremal_of_lt (m : ColumnShape n) {σ : FinPermutation n}
    (hσ : IsMinCosetRep (shapeWeight m) σ) {τ : FinPermutation n} (hτ : τ <ᴮ σ) :
    flagDemazure m τ ⊓ ambientWeight (fun i => (extremalWeight m σ i : ℤ)) = ⊥ := by
  by_contra hne
  have h1 := prefixLE_of_flagDemazure_inf_ne_bot m τ _ hne
  have h2 := prefixLE_permAct_of_le (shapeWeight_antitone m) hτ.1
  have heq := PrefixLE.antisymm h1 h2
  have hw : extremalWeight m τ = extremalWeight m σ := by
    funext i
    exact_mod_cast congrFun heq i
  exact hτ.2 (strongBruhat_antisymm hτ.1 (le_of_extremalWeight_eq m hσ τ hw))

/-! ### Right keys and exact characters -/

open Classical in
/-- A right key of a tuple of row sets, when it has a defining chain. -/
def rightKeyOf (h : Fin d → Fin n) (T : (j : Fin d) → FlagMinorRowSet (h j)) : FinPermutation n :=
  if hT : ∃ w, HasFlagDefiningChain h T w then Classical.choose (exists_rightKey h T hT)
  else Equiv.refl _

theorem hasFlagDefiningChain_iff_rightKeyOf_le {h : Fin d → Fin n}
    {T : (j : Fin d) → FlagMinorRowSet (h j)} (hT : ∃ w, HasFlagDefiningChain h T w)
    (w : FinPermutation n) : HasFlagDefiningChain h T w ↔ rightKeyOf h T ≤ᴮ w := by
  classical
  rw [rightKeyOf, dite_eq_left hT]
  exact Classical.choose_spec (exists_rightKey h T hT) w

/-- The tuples whose right key is exactly `σ`. -/
def exactChainSet (h : Fin d → Fin n) (σ : FinPermutation n) :
    Finset ((j : Fin d) → FlagMinorRowSet (h j)) := by
  classical exact chainSet h {σ} \ chainSet h (schubertBoundary σ)

/-- The generating function of the tuples whose right key is exactly `σ`. -/
def exactCharacter (h : Fin d → Fin n) (σ : FinPermutation n) : Polynomial n :=
  ∑ T ∈ exactChainSet h σ, compositionMonomial (flagTupleWeight h T)

theorem chainSet_boundary_subset (h : Fin d → Fin n) (σ : FinPermutation n) :
    chainSet h (schubertBoundary σ) ⊆ chainSet h {σ} := by
  intro T hT
  obtain ⟨τ, hτ, hc⟩ := mem_chainSet.mp hT
  exact mem_chainSet.mpr ⟨σ, Finset.mem_singleton_self σ, hc.mono (mem_schubertBoundary.mp hτ).1⟩

theorem chainCharacter_singleton_eq (h : Fin d → Fin n) (σ : FinPermutation n) :
    chainCharacter h {σ} = exactCharacter h σ + chainCharacter h (schubertBoundary σ) := by
  classical
  rw [chainCharacter, exactCharacter, chainCharacter, exactChainSet]
  exact (Finset.sum_sdiff (chainSet_boundary_subset h σ)).symm

theorem mem_exactChainSet_iff {h : Fin d → Fin n} {σ : FinPermutation n}
    {T : (j : Fin d) → FlagMinorRowSet (h j)} (hT : ∃ w, HasFlagDefiningChain h T w) :
    T ∈ exactChainSet h σ ↔ rightKeyOf h T = σ := by
  classical
  have hkey := hasFlagDefiningChain_iff_rightKeyOf_le hT
  simp only [exactChainSet, Finset.mem_sdiff, mem_chainSet, Finset.mem_singleton,
    exists_eq_left, mem_schubertBoundary, hkey]
  constructor
  · rintro ⟨hle, hnot⟩
    by_contra hne
    exact hnot ⟨rightKeyOf h T, ⟨hle, hne⟩, strongBruhat_refl _⟩
  · rintro rfl
    refine ⟨strongBruhat_refl _, fun ⟨τ, ⟨hτ, hne⟩, hle⟩ => hne ?_⟩
    exact strongBruhat_antisymm hτ hle

theorem chainCharacter_singleton_eq_sum (h : Fin d → Fin n) (σ : FinPermutation n) :
    chainCharacter h {σ} =
      ∑ τ ∈ insert σ (schubertBoundary σ), exactCharacter h τ := by
  classical
  have hmaps : ∀ T ∈ chainSet h {σ}, rightKeyOf h T ∈ insert σ (schubertBoundary σ) := by
    intro T hT
    obtain ⟨w, hw, hc⟩ := mem_chainSet.mp hT
    rw [Finset.mem_singleton] at hw
    subst hw
    have hle := (hasFlagDefiningChain_iff_rightKeyOf_le ⟨w, hc⟩ w).mp hc
    rw [Finset.mem_insert, mem_schubertBoundary]
    by_cases he : rightKeyOf h T = w
    · exact Or.inl he
    · exact Or.inr ⟨hle, he⟩
  rw [chainCharacter, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun τ hτ => ?_
  rw [exactCharacter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext T
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hT, rfl⟩
    exact (mem_exactChainSet_iff (let ⟨w, _, hc⟩ := mem_chainSet.mp hT; ⟨w, hc⟩)).mpr rfl
  · intro hT
    have hT' : T ∈ chainSet h {τ} := by
      rw [exactChainSet] at hT
      exact (Finset.mem_sdiff.mp hT).1
    obtain ⟨w, hw, hc⟩ := mem_chainSet.mp hT'
    have hkey := (mem_exactChainSet_iff ⟨w, hc⟩).mp hT
    refine ⟨?_, hkey⟩
    rw [Finset.mem_singleton] at hw
    subst hw
    refine mem_chainSet.mpr ⟨σ, Finset.mem_singleton_self σ, ?_⟩
    rcases Finset.mem_insert.mp hτ with h1 | h1
    · rw [← h1]; exact hc
    · exact hc.mono (mem_schubertBoundary.mp h1).1

theorem chainCharacter_singleton (h : Fin d → Fin n) (σ : FinPermutation n) :
    chainCharacter h {σ} = key (extremalWeight (columnMultiplicity h) σ) := by
  apply toLaurent_injective
  apply laurent_ext
  intro μ
  rw [coeff_chainCharacter, ← finrank_flagDemazure_inf h σ μ, finrank_flagDemazure_inf_eq_coeff]

theorem card_chainSet_eq_eval (h : Fin d → Fin n) (S : Finset (FinPermutation n)) :
    ((chainSet h S).card : ℤ) = MvPolynomial.eval (fun _ => (1 : ℤ)) (chainCharacter h S) := by
  simp [chainCharacter, compositionMonomial, MvPolynomial.eval_monomial]

open Classical in
/-- **Exact characters are atoms.** The tuples with right key exactly `σ` have generating
function `𝒜_{σλ}` for `σ ∈ W^λ`, and there are none otherwise. -/
theorem exactCharacter_eq (h : Fin d → Fin n) (σ : FinPermutation n) :
    exactCharacter h σ =
      if IsMinCosetRep (shapeWeight (columnMultiplicity h)) σ then
        atom (extremalWeight (columnMultiplicity h) σ) else 0 := by
  classical
  set m := columnMultiplicity h
  generalize hl : σ.length = l
  induction l using Nat.strong_induction_on generalizing σ with
  | h l ih =>
    by_cases hσ : IsMinCosetRep (shapeWeight m) σ
    · rw [ite_eq_left hσ]
      have hsplit := chainCharacter_singleton_eq_sum h σ
      have hnot : σ ∉ schubertBoundary σ := fun h' =>
        (mem_schubertBoundary.mp h').2 rfl
      rw [chainCharacter_singleton, Finset.sum_insert hnot] at hsplit
      have hlt : ∀ τ ∈ schubertBoundary σ, FinPermutation.length τ < l := by
        intro τ hτ
        rw [← hl]
        have hτ' := mem_schubertBoundary.mp hτ
        exact lt_of_le_of_ne (length_le_of_strongBruhatLE hτ'.1)
          fun he => hτ'.2 (eq_of_strongBruhatLE_of_length_eq hτ'.1 he)
      rw [Finset.sum_congr rfl fun τ hτ => ih _ (hlt τ hτ) τ rfl] at hsplit
      have hBR := key_eq_sum_atom (shapeWeight m) (shapeWeight_antitone m) σ hσ
      have hint : minCosetInterval (shapeWeight m) σ =
          insert σ ((schubertBoundary σ).filter fun τ => IsMinCosetRep (shapeWeight m) τ) := by
        ext τ
        simp only [mem_minCosetInterval, Finset.mem_insert, Finset.mem_filter,
          mem_schubertBoundary]
        constructor
        · rintro ⟨hW, hle⟩
          by_cases he : τ = σ
          · exact Or.inl he
          · exact Or.inr ⟨⟨hle, he⟩, hW⟩
        · rintro (rfl | ⟨⟨hle, -⟩, hW⟩)
          · exact ⟨hσ, strongBruhat_refl _⟩
          · exact ⟨hW, hle⟩
      have hnot' : σ ∉ (schubertBoundary σ).filter fun τ => IsMinCosetRep (shapeWeight m) τ :=
        fun h' => hnot (Finset.mem_filter.mp h').1
      rw [hint, Finset.sum_insert hnot', Finset.sum_filter] at hBR
      rw [← extremalWeight_eq_permAct] at hBR
      simp only [← extremalWeight_eq_permAct] at hBR
      exact add_right_cancel (hsplit.symm.trans hBR)
    · rw [ite_eq_right hσ]
      obtain ⟨τ', hτ'σ, hw⟩ := exists_lt_extremalWeight_eq m σ hσ
      have hsub : chainSet h {τ'} ⊆ chainSet h {σ} := by
        intro T hT
        obtain ⟨w, hw', hc⟩ := mem_chainSet.mp hT
        rw [Finset.mem_singleton] at hw'
        subst hw'
        exact mem_chainSet.mpr ⟨σ, Finset.mem_singleton_self σ, hc.mono hτ'σ.1⟩
      have hcard : (chainSet h {σ}).card ≤ (chainSet h {τ'}).card := by
        have h1 := card_chainSet_eq_eval h {σ}
        have h2 := card_chainSet_eq_eval h {τ'}
        rw [chainCharacter_singleton, ← hw, ← chainCharacter_singleton] at h1
        rw [← h2] at h1
        exact_mod_cast h1.le
      have heq := Finset.eq_of_subset_of_card_le hsub hcard
      have hempty : exactChainSet h σ = ∅ := by
        rw [exactChainSet, Finset.sdiff_eq_empty_iff_subset, ← heq]
        intro T hT
        obtain ⟨w, hw', hc⟩ := mem_chainSet.mp hT
        rw [Finset.mem_singleton] at hw'
        subst hw'
        exact mem_chainSet.mpr ⟨w, mem_schubertBoundary.mpr hτ'σ, hc⟩
      rw [exactCharacter, hempty, Finset.sum_empty]

/-- The character of the boundary: `ch D_{∂σ} = κ_{σλ} − 𝒜_{σλ}` for `σ ∈ W^λ`. -/
theorem chainCharacter_boundary (h : Fin d → Fin n) {σ : FinPermutation n}
    (hσ : IsMinCosetRep (shapeWeight (columnMultiplicity h)) σ) :
    chainCharacter h (schubertBoundary σ) =
      key (extremalWeight (columnMultiplicity h) σ) -
        atom (extremalWeight (columnMultiplicity h) σ) := by
  have h1 := chainCharacter_singleton_eq h σ
  rw [chainCharacter_singleton, exactCharacter_eq, ite_eq_left hσ] at h1
  rw [h1]
  abel

theorem demazureUnion_boundary_hasTorusCharacter (h : Fin d → Fin n) {σ : FinPermutation n}
    (hσ : IsMinCosetRep (shapeWeight (columnMultiplicity h)) σ) :
    HasTorusCharacter (demazureUnionModule (columnMultiplicity h) (schubertBoundary σ)).torus
      (key (extremalWeight (columnMultiplicity h) σ) -
        atom (extremalWeight (columnMultiplicity h) σ)) := by
  rw [← chainCharacter_boundary h hσ]
  exact demazureUnion_hasTorusCharacter h _ (schubertBoundary_bruhatLower σ)

/-- **The extremal weight avoids the boundary** (van der Kallen, Remark 2.3.5): for `σ ∈ W^λ`,
the weight `σλ` does not occur in `D_{∂σ}`. -/
theorem demazureUnion_boundary_inf_extremal (h : Fin d → Fin n) {σ : FinPermutation n}
    (hσ : IsMinCosetRep (shapeWeight (columnMultiplicity h)) σ) :
    demazureUnion (columnMultiplicity h) (schubertBoundary σ) ⊓
      ambientWeight (fun i => (extremalWeight (columnMultiplicity h) σ i : ℤ)) = ⊥ := by
  classical
  apply Submodule.finrank_eq_zero.mp
  rw [finrank_demazureUnion_inf_eq h _ (schubertBoundary_bruhatLower σ), chainCount,
    Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro T hT hwt
  obtain ⟨τ, hτ, hc⟩ := mem_chainSet.mp hT
  have hcount : 0 < chainCount h {τ}
      (fun i => (extremalWeight (columnMultiplicity h) σ i : ℤ)) := by
    unfold chainCount
    exact Finset.card_pos.mpr ⟨T, Finset.mem_filter.mpr
      ⟨mem_chainSet.mpr ⟨τ, Finset.mem_singleton_self τ, hc⟩, hwt⟩⟩
  rw [← finrank_flagDemazure_inf, flagDemazure_inf_extremal_of_lt _ hσ
    (mem_schubertBoundary.mp hτ), finrank_bot] at hcount
  exact lt_irrefl 0 hcount

end

end Demazure.SchubertUnions
