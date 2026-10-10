import RSCounterexample.Paper.Quiver.Schur.Pieri
import TauCeti.Combinatorics.Young.Interlacing

/-!
# Young's rule in projector form

The multiplicity of `s_λ` in a product `h_{r_0} ⋯ h_{r_{K−1}}` of complete homogeneous symmetric
polynomials in `d` variables is the Kostka number `K_{λ r}`, the number of semistandard tableaux of
shape `λ` and content `r` (`weylProjector_prod_hsymm`).

The proof is by induction on `K`. Multiplying by the last factor `h_{r_{K−1}}` acts on Schur
coefficients by the Pieri rule (`alternant_mul_hsymm_pieri`, through the Weyl projector:
`weylProjector_mul_hsymm`), and Kostka numbers satisfy the same recursion, by erasing the largest
letter of a tableau (Tau Ceti's branching bijection `TauCeti.BoundedSSYT.fiberEquiv`):
`kostka_succ`.

## Main definitions

* `Schubert.RS.Quiver.Schur.contentOf`: the content `k ↦ r_k` of a finite sequence.
* `Schubert.RS.Quiver.Schur.pieriCount`: the number (zero or one) of Pieri steps between two
  weights.

## Main results

* `Schubert.RS.Quiver.Schur.kostka_succ`: the branching recursion for Kostka numbers.
* `Schubert.RS.Quiver.Schur.weylProjector_mul_hsymm`: the Pieri rule for Weyl projectors.
* `Schubert.RS.Quiver.Schur.weylProjector_prod_hsymm`: Young's rule.
-/

namespace Schubert.RS.Quiver.Schur

noncomputable section

open Equiv

/-! ## Contents of finite sequences -/

/-- The content `k ↦ r_k` of a finite sequence `r_0, …, r_{K−1}` (zero from `K` on): the letter `k`
is used `r_k` times. -/
def contentOf {K : ℕ} (r : Fin K → ℕ) : ℕ → ℕ := fun k => if h : k < K then r ⟨k, h⟩ else 0

theorem contentOf_of_le {K : ℕ} (r : Fin K → ℕ) {k : ℕ} (hk : K ≤ k) : contentOf r k = 0 := by
  simp [contentOf, not_lt.mpr hk]

theorem contentOf_last {K : ℕ} (r : Fin (K + 1) → ℕ) : contentOf r K = r (Fin.last K) := by
  simp [contentOf, Fin.last]

theorem contentOf_castSucc {K : ℕ} (r : Fin (K + 1) → ℕ) {k : ℕ} (hk : k < K) :
    contentOf (fun i : Fin K => r i.castSucc) k = contentOf r k := by
  simp [contentOf, hk, Nat.lt_succ_of_lt hk, Fin.castSucc]

/-! ## Kostka numbers and their branching recursion -/

section Kostka

open TauCeti

/-- A tableau whose content vanishes from `K` on uses only the letters `< K`. -/
theorem entry_lt_of_content {μ : YoungDiagram} {K : ℕ} (T : _root_.SemistandardYoungTableau μ)
    (hT : ∀ k, K ≤ k → SemistandardYoungTableau.content T k = 0) {i c : ℕ} (h : (i, c) ∈ μ) :
    T i c < K := by
  by_contra hlt
  have h0 := hT (T i c) (not_lt.mp hlt)
  rw [SemistandardYoungTableau.content_apply, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff] at h0
  exact h0 ((_root_.YoungDiagram.mem_cells _).mpr h) rfl

/-- The content of a tableau in the letters `< n` vanishes from `n` on. -/
theorem content_eq_zero_of_le {μ : YoungDiagram} {n : ℕ} (T : BoundedSSYT n μ) {k : ℕ}
    (hk : n ≤ k) : SemistandardYoungTableau.content T.1 k = 0 := by
  rw [SemistandardYoungTableau.content_apply, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro c hc heq
  have := BoundedSSYT.entry_lt T ((_root_.YoungDiagram.mem_cells _).mp hc)
  omega

/-- Kostka numbers count bounded tableaux. -/
theorem diagramKostkaNumber_eq_card {μ : YoungDiagram} {K : ℕ} (w : ℕ → ℕ)
    (hw : ∀ k, K ≤ k → w k = 0) :
    diagramKostkaNumber μ w =
      Nat.card {T : BoundedSSYT K μ // ⇑(SemistandardYoungTableau.content T.1) = w} := by
  rw [diagramKostkaNumber_def]
  refine Nat.card_congr
    { toFun := fun T => ⟨⟨T.1, fun i c h => entry_lt_of_content T.1
          (fun k hk => (congrFun T.2 k).trans (hw k hk)) h⟩, T.2⟩
      invFun := fun T => ⟨T.1.1, T.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- A Kostka number vanishes when the shape is taller than the alphabet. -/
theorem diagramKostkaNumber_eq_zero_of_lt_colLen {μ : YoungDiagram} {K : ℕ} (w : ℕ → ℕ)
    (hw : ∀ k, K ≤ k → w k = 0) (hμ : K < μ.colLen 0) : diagramKostkaNumber μ w = 0 := by
  rw [diagramKostkaNumber_eq_card w hw]
  have := BoundedSSYT.isEmpty_of_lt_colLen (μ := μ) hμ
  exact Nat.card_of_isEmpty

/-- Erasing the largest letter `K` of a tableau in the letters `≤ K`: the cells of the sub-shape of
smaller letters, and the number of cells carrying `K`. -/
theorem card_eq_card_restrictShape_add {μ : YoungDiagram} {K : ℕ} (T : BoundedSSYT (K + 1) μ) :
    μ.card = (BoundedSSYT.restrictShape T).card + SemistandardYoungTableau.content T.1 K := by
  have hcells : (BoundedSSYT.restrictShape T).cells = μ.cells.filter fun c => T.1 c.1 c.2 < K := by
    ext ⟨i, j⟩
    simp [_root_.YoungDiagram.mem_cells, BoundedSSYT.mem_restrictShape]
  have hK : (μ.cells.filter fun c => ¬ T.1 c.1 c.2 < K) =
      μ.cells.filter fun c => T.1 c.1 c.2 = K := by
    refine Finset.filter_congr fun c hc => ?_
    have := BoundedSSYT.entry_lt T ((_root_.YoungDiagram.mem_cells _).mp hc)
    omega
  rw [YoungDiagram.card, YoungDiagram.card, hcells, SemistandardYoungTableau.content_apply, ← hK,
    Finset.card_filter_add_card_filter_not]

/-- **The branching recursion for Kostka numbers**: erasing the largest letter, a tableau of shape
`μ` and content `r` is a tableau of a shape `ν` interlacing `μ`, with content `r` without its last
entry, and `|μ| − |ν|` is the last entry of `r`. -/
theorem kostka_succ {K : ℕ} (μ : YoungDiagram) (r : Fin (K + 1) → ℕ) :
    diagramKostkaNumber μ (contentOf r) =
      ∑ ν ∈ YoungDiagram.interlacingShapes K μ,
        if μ.card = ν.card + r (Fin.last K) then
          diagramKostkaNumber ν (contentOf fun i : Fin K => r i.castSucc) else 0 := by
  classical
  set r' : Fin K → ℕ := fun i => r i.castSucc
  have hw : ∀ k, K + 1 ≤ k → contentOf r k = 0 := fun k hk => contentOf_of_le r hk
  have hw' : ∀ k, K ≤ k → contentOf r' k = 0 := fun k hk => contentOf_of_le r' hk
  rw [diagramKostkaNumber_eq_card _ hw, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  -- the condition on a tableau in terms of its restriction
  have key : ∀ T : BoundedSSYT (K + 1) μ,
      (⇑(SemistandardYoungTableau.content T.1) = contentOf r) ↔
        (μ.card = (BoundedSSYT.restrictShape T).card + r (Fin.last K) ∧
          ⇑(SemistandardYoungTableau.content
            (BoundedSSYT.restrict T (BoundedSSYT.restrictShape T) rfl).1) = contentOf r') := by
    intro T
    have hcard := card_eq_card_restrictShape_add T
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · rw [hcard, congrFun h K, contentOf_last]
      · funext k
        rcases Nat.lt_or_ge k K with hk | hk
        · rw [BoundedSSYT.content_restrict _ _ hk, congrFun h k, contentOf_castSucc r hk]
        · rw [content_eq_zero_of_le _ hk, hw' k hk]
    · rintro ⟨h1, h2⟩
      funext k
      rcases Nat.lt_or_ge k K with hk | hk
      · rw [← BoundedSSYT.content_restrict T rfl hk, congrFun h2 k, contentOf_castSucc r hk]
      · rcases Nat.eq_or_lt_of_le hk with hk' | hk'
        · subst hk'
          rw [contentOf_last]
          omega
        · rw [content_eq_zero_of_le T hk', hw k hk']
  simp only [key]
  refine (BoundedSSYT.sum_eq_sum_interlacingShapes K μ (M := ℕ) fun ν T' =>
    if μ.card = ν.card + r (Fin.last K) ∧
      ⇑(SemistandardYoungTableau.content T'.1) = contentOf r' then 1 else 0).trans ?_
  refine Finset.sum_congr rfl fun ν _ => ?_
  by_cases hν : μ.card = ν.card + r (Fin.last K)
  · rw [ite_eq_left hν, diagramKostkaNumber_eq_card _ hw', Nat.card_eq_fintype_card,
      Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
    simp only [hν, true_and]
  · rw [ite_eq_right hν]
    simp [hν]

end Kostka

/-! ## The Pieri rule for Weyl projectors -/

variable {d : ℕ}

/-- The number of Pieri steps by `h_s` from `ν` to `λ`: one if `λ − ν` is a horizontal strip of size
`s`, zero otherwise. -/
def pieriCount (ν lam : Weight d) (s : ℕ) : ℕ :=
  ((pieriSet ν s).filter fun u => ν + liftW u = lam).card

theorem coeff_alternant_mul_hsymm {κ lam : Weight d} (hκ : Antitone κ) (hlam : Antitone lam)
    (s : ℕ) :
    (alternant (κ + staircase d) * toLaurent (MvPolynomial.hsymm (Fin d) ℤ s)).coeff
      (lam + staircase d) = pieriCount κ lam s := by
  classical
  rw [alternant_mul_hsymm_pieri hκ, AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum,
    Finset.sum_apply, pieriCount, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [coeff_alternant_of_strictAnti
    (strictAnti_add_staircase (antitone_add_of_mem_pieriSet hκ hu))
    (strictAnti_add_staircase hlam)]
  simp only [add_left_inj]
  split_ifs <;> simp

theorem comp_revPerm_comp_revPerm (u : Weight d) :
    (u ∘ ⇑(Fin.revPerm : Perm (Fin d))) ∘ ⇑(Fin.revPerm : Perm (Fin d)) = u := by
  funext i
  simp

/-- **The Pieri rule for Weyl projectors**: the Schur coefficients of `f · h_s` are obtained from
those of `f` by Pieri steps. The sum may run over any finite set of dominant weights containing the
ones that contribute. -/
theorem weylProjector_mul_hsymm {f : Laurent d} (hf : IsSymmetric f) (s : ℕ)
    (lam : TauCeti.DominantWeight d) (T : Finset (TauCeti.DominantWeight d))
    (hT : ∀ ν : TauCeti.DominantWeight d,
      weylProjector (ν.1 ∘ ⇑(Fin.revPerm : Perm (Fin d))) f ≠ 0 →
        pieriCount ν.1 lam.1 s ≠ 0 → ν ∈ T) :
    weylProjector (lam.1 ∘ ⇑(Fin.revPerm : Perm (Fin d)))
        (f * toLaurent (MvPolynomial.hsymm (Fin d) ℤ s)) =
      ∑ ν ∈ T, weylProjector (ν.1 ∘ ⇑(Fin.revPerm : Perm (Fin d))) f * pieriCount ν.1 lam.1 s := by
  classical
  set c : TauCeti.DominantWeight d → ℤ :=
    fun ν => weylProjector (ν.1 ∘ ⇑(Fin.revPerm : Perm (Fin d))) f with hc
  have hsym : IsSymmetric (f * toLaurent (MvPolynomial.hsymm (Fin d) ℤ s)) :=
    hf.mul (isSymmetric_toLaurent_hsymm s)
  obtain ⟨S, hS⟩ := exists_eq_sum_ratSchur hf
  have hcS : ∀ ν, c ν = if ν ∈ S then c ν else 0 := by
    intro ν
    have h := weylProjector_sum_ratSchur S c ν
    rw [← hS] at h
    exact h
  rw [weylProjector_eq_alternant hsym, comp_revPerm_comp_revPerm]
  have hexp : alternant (staircase d) * (f * toLaurent (MvPolynomial.hsymm (Fin d) ℤ s)) =
      ∑ ν ∈ S, (c ν : Laurent d) *
        (alternant (ν.1 + staircase d) * toLaurent (MvPolynomial.hsymm (Fin d) ℤ s)) := by
    conv_lhs => rw [hS]
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [← alternant_mul_ratSchur]
    ring
  rw [hexp, AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  have hterm : ∀ ν : TauCeti.DominantWeight d, ((c ν : Laurent d) *
      (alternant (ν.1 + staircase d) * toLaurent (MvPolynomial.hsymm (Fin d) ℤ s))).coeff
        (lam.1 + staircase d) = c ν * pieriCount ν.1 lam.1 s := by
    intro ν
    rw [AddMonoidAlgebra.intCast_def, coeff_single_zero_mul,
      coeff_alternant_mul_hsymm ν.2 lam.2, Int.cast_id]
  simp only [hterm]
  calc ∑ ν ∈ S, c ν * (pieriCount ν.1 lam.1 s : ℤ)
      = ∑ ν ∈ S ∪ T, c ν * (pieriCount ν.1 lam.1 s : ℤ) := by
        apply Finset.sum_subset Finset.subset_union_left
        intro ν _ hν
        rw [hcS ν, ite_eq_right hν, zero_mul]
    _ = ∑ ν ∈ T, c ν * (pieriCount ν.1 lam.1 s : ℤ) := by
        symm
        apply Finset.sum_subset Finset.subset_union_right
        intro ν _ hν
        by_contra hne
        apply hν
        apply hT ν
        · exact fun h => hne (by rw [show c ν = 0 from h, zero_mul])
        · exact fun h => hne (by rw [h, Nat.cast_zero, mul_zero])

/-! ## Young's rule -/

/-- The product `h_{r_0} ⋯ h_{r_{K−1}}` in `Laurent d`. -/
def hProd (d : ℕ) {K : ℕ} (r : Fin K → ℕ) : Laurent d :=
  toLaurent (∏ k, MvPolynomial.hsymm (Fin d) ℤ (r k))

theorem hProd_succ {K : ℕ} (r : Fin (K + 1) → ℕ) :
    hProd d r = hProd d (fun k : Fin K => r k.castSucc) *
      toLaurent (MvPolynomial.hsymm (Fin d) ℤ (r (Fin.last K))) := by
  simp only [hProd, Fin.prod_univ_castSucc, map_mul]

theorem isSymmetric_hProd {K : ℕ} (r : Fin K → ℕ) : IsSymmetric (hProd d r) := by
  apply isSymmetric_toLaurent
  rw [← MvPolynomial.mem_symmetricSubalgebra]
  exact Subalgebra.prod_mem _ fun k _ =>
    (MvPolynomial.mem_symmetricSubalgebra _).mpr (MvPolynomial.hsymm_isSymmetric _ _ _)

instance instDecidableIsPolynomial (lam : TauCeti.DominantWeight d) :
    Decidable lam.IsPolynomial :=
  decidable_of_iff _ (TauCeti.DominantWeight.isPolynomial_iff_zero_le_detShift lam).symm

/-- The Kostka number at a dominant weight, zero at weights with negative entries. -/
def kostkaZ {K : ℕ} (r : Fin K → ℕ) (lam : TauCeti.DominantWeight d) : ℤ :=
  if lam.IsPolynomial then (TauCeti.diagramKostkaNumber lam.shape (contentOf r) : ℤ) else 0

theorem isPolynomial_of_pieriCount_ne_zero {ν lam : TauCeti.DominantWeight d} {s : ℕ}
    (hν : ν.IsPolynomial) (h : pieriCount ν.1 lam.1 s ≠ 0) : lam.IsPolynomial := by
  obtain ⟨u, hu⟩ := Finset.card_ne_zero.mp h
  have hu' := (Finset.mem_filter.mp hu).2
  intro i
  rw [← hu']
  simp only [Pi.add_apply, liftW_apply]
  have := hν i
  positivity

/-- The Pieri step from the weight of `ρ` to `λ`, when `ρ` interlaces the shape of `λ`. -/
theorem pieriCount_weightOfShape {lam : TauCeti.DominantWeight d} (hlam : lam.IsPolynomial)
    {ρ : YoungDiagram} (hρ : YoungDiagram.InterlacedBy lam.shape ρ) (s : ℕ) :
    pieriCount (TauCeti.weightOfShape d ρ).1 lam.1 s =
      if lam.shape.card = ρ.card + s then 1 else 0 := by
  classical
  set u₀ : Fin d → ℕ := fun i => lam.shape.rowLen i - ρ.rowLen i
  have hrow : ∀ i : Fin d, (lam.shape.rowLen i : ℤ) = lam.1 i :=
    TauCeti.DominantWeight.natCast_rowLen_shape hlam
  have hle : ∀ i : ℕ, ρ.rowLen i ≤ lam.shape.rowLen i := hρ.rowLen_le
  have hsum0 : (TauCeti.weightOfShape d ρ).1 + liftW u₀ = lam.1 := by
    funext i
    simp only [Pi.add_apply, liftW_apply, TauCeti.weightOfShape_apply, u₀]
    rw [← hrow i]
    have := hle i
    push_cast [Nat.cast_sub this]
    ring
  have hρd : ρ.colLen 0 ≤ d := by
    by_contra h
    have hm : ((d, 0) : ℕ × ℕ) ∈ ρ := YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_not_le h)
    have h1 := YoungDiagram.mem_iff_lt_rowLen.mp hm
    have h2 := hle d
    rw [TauCeti.DominantWeight.rowLen_shape_eq_zero_of_le lam le_rfl] at h2
    omega
  have hcardρ : (ρ.card : ℤ) = ∑ i : Fin d, (ρ.rowLen i : ℤ) := by
    have h := TauCeti.DominantWeight.natCast_card_shape (TauCeti.isPolynomial_weightOfShape d ρ)
    rw [TauCeti.shape_weightOfShape hρd] at h
    simpa using h
  have hcardL : (lam.shape.card : ℤ) = ∑ i : Fin d, (lam.shape.rowLen i : ℤ) := by
    rw [TauCeti.DominantWeight.natCast_card_shape hlam]
    exact Finset.sum_congr rfl fun i _ => (hrow i).symm
  have hsumu : ((∑ i, u₀ i : ℕ) : ℤ) = lam.shape.card - ρ.card := by
    rw [hcardρ, hcardL, Nat.cast_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [u₀]
    push_cast [Nat.cast_sub (hle i)]
    ring
  have hviol : ∀ i, ¬ Violates (TauCeti.weightOfShape d ρ).1 u₀ i := by
    rintro i ⟨hi, hv⟩
    simp only [TauCeti.weightOfShape_apply, u₀] at hv
    have h1 := hρ.rowLen_succ_le (prev i).val
    have h2 : (prev i).val + 1 = i.val := by rw [prev_val]; omega
    rw [h2] at h1
    push_cast [Nat.cast_sub (hle i)] at hv
    omega
  have huniq : ∀ u ∈ (pieriSet (TauCeti.weightOfShape d ρ).1 s).filter
      (fun u => (TauCeti.weightOfShape d ρ).1 + liftW u = lam.1), u = u₀ := by
    intro u hu
    have h := (Finset.mem_filter.mp hu).2
    rw [← hsum0] at h
    funext i
    have := congrFun h i
    simp only [Pi.add_apply, liftW_apply, add_right_inj] at this
    exact_mod_cast this
  by_cases hc : lam.shape.card = ρ.card + s
  · rw [ite_eq_left hc, pieriCount, Finset.card_eq_one]
    refine ⟨u₀, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, huniq⟩⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, hviol⟩, hsum0⟩
    rw [mem_compositionsOf]
    have : ((∑ i, u₀ i : ℕ) : ℤ) = s := by rw [hsumu, hc]; push_cast; ring
    exact_mod_cast this
  · rw [ite_eq_right hc, pieriCount, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro u hu
    have hu0 := huniq u hu
    subst hu0
    have hs := mem_compositionsOf.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).1
    apply hc
    have : (lam.shape.card : ℤ) = ρ.card + s := by rw [← hs, hsumu]; ring
    exact_mod_cast this

/-- The Kostka numbers of the empty content: one at the zero weight, zero elsewhere. -/
theorem kostkaZ_zero (r : Fin 0 → ℕ) (lam : TauCeti.DominantWeight d) :
    kostkaZ r lam = if lam.1 = 0 then 1 else 0 := by
  have hc : contentOf r = 0 := funext fun k => contentOf_of_le r (Nat.zero_le k)
  unfold kostkaZ
  by_cases hp : lam.IsPolynomial
  · rw [ite_eq_left hp, hc]
    by_cases h0 : lam.1 = 0
    · rw [ite_eq_left h0]
      have hrow : lam.shape.rowLen = 0 := by
        funext i
        rcases Nat.lt_or_ge i d with hi | hi
        · have := TauCeti.DominantWeight.rowLen_shape lam ⟨i, hi⟩
          simp only [h0, Pi.zero_apply, Int.toNat_zero] at this
          exact this
        · exact TauCeti.DominantWeight.rowLen_shape_eq_zero_of_le lam hi
      have h1 := TauCeti.diagramKostkaNumber_rowLen lam.shape
      rw [hrow] at h1
      rw [h1, Nat.cast_one]
    · rw [ite_eq_right h0]
      obtain ⟨i, hi⟩ : ∃ i, lam.1 i ≠ 0 := by
        by_contra h
        push Not at h
        exact h0 (funext h)
      have hd : 0 < d := lt_of_le_of_lt (Nat.zero_le _) i.isLt
      have hpos : 0 < lam.1 ⟨0, hd⟩ := lt_of_lt_of_le (lt_of_le_of_ne (hp i) (Ne.symm hi))
        (lam.2 (Fin.le_def.mpr (Nat.zero_le i.val)))
      have hmem : ((0, 0) : ℕ × ℕ) ∈ lam.shape := by
        rw [YoungDiagram.mem_iff_lt_rowLen]
        have := TauCeti.DominantWeight.rowLen_shape lam ⟨0, hd⟩
        simp only at this
        rw [this]
        omega
      have hk : TauCeti.diagramKostkaNumber lam.shape 0 = 0 := by
        by_contra hne
        obtain ⟨T, hT⟩ := TauCeti.diagramKostkaNumber_ne_zero_iff.mp hne
        have h0' := congrFun hT (T 0 0)
        rw [SemistandardYoungTableau.content_apply, Pi.zero_apply, Finset.card_eq_zero,
          Finset.filter_eq_empty_iff] at h0'
        exact h0' ((_root_.YoungDiagram.mem_cells _).mpr hmem) rfl
      rw [hk, Nat.cast_zero]
  · rw [ite_eq_right hp]
    have h0 : lam.1 ≠ 0 := fun h => hp fun i => by rw [h]; rfl
    rw [ite_eq_right h0]

theorem weylProjector_one (lam : TauCeti.DominantWeight d) :
    weylProjector (lam.1 ∘ ⇑(Fin.revPerm : Perm (Fin d))) 1 = if lam.1 = 0 then 1 else 0 := by
  rw [weylProjector_eq_alternant (fun σ => map_one _), comp_revPerm_comp_revPerm, mul_one,
    coeff_alternant_of_strictAnti (staircase_strictAnti d) (strictAnti_add_staircase lam.2)]
  by_cases h : lam.1 = 0
  · rw [ite_eq_left h, ite_eq_left (by rw [h, zero_add])]
  · rw [ite_eq_right h, ite_eq_right]
    intro h'
    apply h
    have := congrArg (fun v => v - staircase d) h'
    simpa using this.symm

/-- **The Schur coefficients of `h_{r_0} ⋯ h_{r_{K−1}}` are Kostka numbers**, at every dominant
weight. -/
theorem weylProjector_hProd {K : ℕ} (r : Fin K → ℕ) (lam : TauCeti.DominantWeight d) :
    weylProjector (lam.1 ∘ ⇑(Fin.revPerm : Perm (Fin d))) (hProd d r) = kostkaZ r lam := by
  induction K generalizing lam with
  | zero =>
    have h1 : hProd d r = 1 := by simp [hProd]
    rw [h1, weylProjector_one, kostkaZ_zero]
  | succ K ih =>
    classical
    rw [hProd_succ]
    set r' : Fin K → ℕ := fun k => r k.castSucc with hr'
    set s := r (Fin.last K) with hs
    by_cases hp : lam.IsPolynomial
    · set μ := lam.shape
      rw [weylProjector_mul_hsymm (isSymmetric_hProd r') s lam
        ((YoungDiagram.interlacingShapes d μ).image (TauCeti.weightOfShape d))]
      · rw [Finset.sum_image]
        · have hK := kostka_succ μ r
          unfold kostkaZ
          rw [ite_eq_left hp, hK]
          push_cast
          -- compare the two sums over interlacing shapes, with at most `d` and at most `K` rows
          have hbig : ∀ n, n ≤ d + K → YoungDiagram.interlacingShapes n μ ⊆
              YoungDiagram.interlacingShapes (d + K) μ := by
            intro n hn ρ hρ
            rw [YoungDiagram.mem_interlacingShapes] at hρ ⊢
            exact ⟨hρ.1, hρ.2.trans hn⟩
          have hrows : ∀ ρ, YoungDiagram.InterlacedBy μ ρ → ρ.colLen 0 ≤ d := by
            intro ρ hρ
            by_contra h
            have hm : ((d, 0) : ℕ × ℕ) ∈ ρ :=
              YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_not_le h)
            have h1 := YoungDiagram.mem_iff_lt_rowLen.mp hm
            have h2 := hρ.rowLen_le d
            rw [TauCeti.DominantWeight.rowLen_shape_eq_zero_of_le lam le_rfl] at h2
            omega
          rw [Finset.sum_subset (hbig d (Nat.le_add_right d K)),
            Finset.sum_subset (hbig K (Nat.le_add_left K d))]
          · refine Finset.sum_congr rfl fun ρ hρ => ?_
            have hρ' := YoungDiagram.mem_interlacingShapes.mp hρ
            have hρd := hrows ρ hρ'.1
            rw [ih, pieriCount_weightOfShape hp hρ'.1]
            unfold kostkaZ
            rw [ite_eq_left (TauCeti.isPolynomial_weightOfShape d ρ),
              TauCeti.shape_weightOfShape hρd]
            split_ifs <;> simp [hr']
          · intro ρ hρ hρK
            rw [YoungDiagram.mem_interlacingShapes] at hρ hρK
            have hlt : K < ρ.colLen 0 := by
              by_contra h
              exact hρK ⟨hρ.1, Nat.le_of_not_lt h⟩
            rw [diagramKostkaNumber_eq_zero_of_lt_colLen _ (fun k hk => contentOf_of_le r' hk)
              hlt]
            simp
          · intro ρ hρ hρd
            rw [YoungDiagram.mem_interlacingShapes] at hρ hρd
            exact absurd ⟨hρ.1, hrows ρ hρ.1⟩ hρd
        · intro ρ₁ h₁ ρ₂ h₂ heq
          have e₁ := TauCeti.shape_weightOfShape (YoungDiagram.mem_interlacingShapes.mp h₁).2
          have e₂ := TauCeti.shape_weightOfShape (YoungDiagram.mem_interlacingShapes.mp h₂).2
          rw [← e₁, ← e₂]
          exact congrArg TauCeti.DominantWeight.shape heq
      · intro ν hν hc
        rw [ih] at hν
        have hνp : ν.IsPolynomial := by
          by_contra h
          exact hν (by unfold kostkaZ; rw [ite_eq_right h])
        obtain ⟨u, hu⟩ := Finset.card_ne_zero.mp hc
        have hu1 := (Finset.mem_filter.mp hu).2
        have hu2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2
        refine Finset.mem_image.mpr ⟨ν.shape, YoungDiagram.mem_interlacingShapes.mpr ⟨?_,
          TauCeti.DominantWeight.colLen_zero_shape_le ν⟩, TauCeti.weightOfShape_shape hνp⟩
        refine YoungDiagram.interlacedBy_iff.mpr fun i => ?_
        rcases Nat.lt_or_ge i d with hi | hi
        · have eL := TauCeti.DominantWeight.natCast_rowLen_shape hp ⟨i, hi⟩
          have eν := TauCeti.DominantWeight.natCast_rowLen_shape hνp ⟨i, hi⟩
          have hLi := congrFun hu1 ⟨i, hi⟩
          simp only [Pi.add_apply, liftW_apply] at hLi
          refine ⟨?_, ?_⟩
          · rcases Nat.lt_or_ge (i + 1) d with hi1 | hi1
            · have eL1 := TauCeti.DominantWeight.natCast_rowLen_shape hp ⟨i + 1, hi1⟩
              have hL1 := congrFun hu1 ⟨i + 1, hi1⟩
              simp only [Pi.add_apply, liftW_apply] at hL1
              have hv := hu2 ⟨i + 1, hi1⟩
              simp only [Violates, prev, not_and, not_lt] at hv
              have hv' := hv (Nat.succ_pos i)
              have hprev : (⟨i + 1 - 1, by omega⟩ : Fin d) = ⟨i, hi⟩ := by ext; simp
              rw [hprev] at hv'
              have : (μ.rowLen (i + 1) : ℤ) ≤ ν.shape.rowLen i := by
                simp only [μ]
                rw [eL1, eν, ← hL1]
                exact hv'
              exact_mod_cast this
            · rw [TauCeti.DominantWeight.rowLen_shape_eq_zero_of_le lam hi1]
              exact Nat.zero_le _
          · have : (ν.shape.rowLen i : ℤ) ≤ μ.rowLen i := by
              simp only [μ]
              rw [eL, eν, ← hLi]
              have := (u ⟨i, hi⟩).cast_nonneg (α := ℤ)
              linarith
            exact_mod_cast this
        · rw [TauCeti.DominantWeight.rowLen_shape_eq_zero_of_le ν hi]
          refine ⟨?_, Nat.zero_le _⟩
          rw [show μ.rowLen (i + 1) = 0 from
            TauCeti.DominantWeight.rowLen_shape_eq_zero_of_le lam (by omega)]
    · rw [weylProjector_mul_hsymm (isSymmetric_hProd r') s lam ∅]
      · unfold kostkaZ
        rw [ite_eq_right hp, Finset.sum_empty]
      · intro ν hν hc
        rw [ih] at hν
        have hνp : ν.IsPolynomial := by
          by_contra h
          exact hν (by unfold kostkaZ; rw [ite_eq_right h])
        exact absurd (isPolynomial_of_pieriCount_ne_zero hνp hc) hp

/-- **Young's rule in projector form**: for a Young diagram `μ` with at most `d` rows, the
coefficient of `s_μ` in `h_{r_0} ⋯ h_{r_{K−1}}` (in `d` variables) is the Kostka number `K_{μ r}`,
the number of semistandard tableaux of shape `μ` and content `r`. -/
theorem weylProjector_prod_hsymm {K : ℕ} (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ d)
    (r : Fin K → ℕ) :
    weylProjector ((TauCeti.weightOfShape d μ).1 ∘ ⇑(Fin.revPerm : Perm (Fin d)))
        (toLaurent (∏ k, MvPolynomial.hsymm (Fin d) ℤ (r k))) =
      TauCeti.diagramKostkaNumber μ (contentOf r) := by
  have h := weylProjector_hProd r (TauCeti.weightOfShape d μ)
  rw [hProd] at h
  rw [h]
  unfold kostkaZ
  rw [ite_eq_left (TauCeti.isPolynomial_weightOfShape d μ), TauCeti.shape_weightOfShape hμ]

end

end Schubert.RS.Quiver.Schur
