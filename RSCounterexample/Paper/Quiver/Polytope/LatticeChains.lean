import RSCounterexample.Paper.Quiver.Polytope.LatticeSlots
import RSCounterexample.Paper.Quiver.Polytope.Decode

/-!
# The conditions of the polytope are the conditions of LR chains

Let positional data `P` realize a forward quiver `Q` with weight `λ`
(`Schubert.RS.Quiver.Flat.PositionalQuiver.Realizes`). Take arrow shapes `μ` and, at every vertex
`p`, a tableau `T p t` for every factor `t` at `p`
(`Schubert.RS.Quiver.ForwardQuiver.Tabs`). Coordinates `sh`, `ce` of `P` *agree* with `(μ, T)`
(`Schubert.RS.Quiver.Flat.PositionalQuiver.Realizes.Agrees`) when the partition coordinates of
each arrow are the rows of its shape, the row-count coordinates of each factor are the row counts
of its tableau, and all other coordinates on the index box vanish.

For agreeing coordinates, the six families of conditions of `P`
(`Schubert.RS.Quiver.Flat.PositionalQuiver.Conditions`) hold exactly when every `T p` is an LR
chain for the factors at `p` ending at `λ^{(p)}`
(`Schubert.RS.Quiver.Flat.PositionalQuiver.Realizes.Agrees.conditions_iff`): families 1–4 hold
automatically, family 5 is the lattice condition of each tableau from the weight accumulated
before it, and family 6 is the final weight.

## Main definitions

* `Schubert.RS.Quiver.ForwardQuiver.Tabs`: a tableau for every factor at every vertex.
* `Schubert.RS.Quiver.Flat.PositionalQuiver.Realizes.Agrees`.

## Main results

* `Schubert.RS.Quiver.Flat.PositionalQuiver.Realizes.Agrees.conditions_iff`.
-/

namespace Schubert.RS.Quiver

open Finset SemistandardYoungTableau Schubert.RS.LR Schubert.RS.Quiver.Schur

namespace ForwardQuiver

variable (Q : ForwardQuiver)

/-- A tableau in the letters `0, …, d_p − 1` for every factor `t` at every vertex `p`, of the shape
of the factor. -/
abbrev Tabs (μ : Q.ArrowShapes) : Type :=
  (p : Fin Q.s) → (t : Fin (Q.valence p)) →
    TauCeti.BoundedSSYT (Q.dim p) (Q.vertexFactors μ p t).shape

variable {Q}

theorem colLen_vertexFactors (μ : Q.ArrowShapes) (p : Fin Q.s) (t : Fin (Q.valence p)) :
    (Q.vertexFactors μ p t).shape.colLen 0 ≤ Q.dim p := by
  rw [Q.vertexFactors_eq]
  split_ifs with h
  · exact (μ _).2.trans ((min_le_left _ _).trans_eq (congrArg Q.dim h))
  · exact TauCeti.DominantWeight.colLen_zero_shape_le _

theorem rowLen_vertexFactors (μ : Q.ArrowShapes) (p : Fin Q.s) (t : Fin (Q.valence p)) {r : ℕ}
    (hr : r < Q.dim p) :
    ((Q.vertexFactors μ p t).shape.rowLen r : ℤ) =
      if Q.src (Q.arrowAt p t) = p then ((μ (Q.arrowAt p t)).1.rowLen r : ℤ)
      else ((μ (Q.arrowAt p t)).1.rowLen 0 : ℤ) -
        (μ (Q.arrowAt p t)).1.rowLen (Q.dim p - 1 - r) := by
  rw [Q.vertexFactors_eq]
  split_ifs with h
  · rfl
  · rw [rowLen_inFactor_shape _ _ hr,
      Nat.cast_sub ((μ (Q.arrowAt p t)).1.rowLen_anti 0 _ (Nat.zero_le _))]

theorem shift_vertexFactors (μ : Q.ArrowShapes) (p : Fin Q.s) (t : Fin (Q.valence p)) :
    (Q.vertexFactors μ p t).shift =
      if Q.src (Q.arrowAt p t) = p then 0 else -((μ (Q.arrowAt p t)).1.rowLen 0 : ℤ) := by
  rw [Q.vertexFactors_eq]
  split_ifs with h
  · rfl
  · exact shift_inFactor _ _ ((μ _).2.trans
      ((min_le_right _ _).trans_eq (congrArg Q.dim (Q.tgt_eq_of_src_ne h))))

end ForwardQuiver

namespace Flat

/-! ### Row counts of bounded tableaux -/

section RowCounts

variable {d : ℕ} {ν : YoungDiagram}

theorem rowCountLt_eq_rowLen_of_le (T : TauCeti.BoundedSSYT d ν) (r : ℕ) {x : ℕ} (hx : d ≤ x) :
    rowCountLt T.1 r x = ν.rowLen r := by
  have h1 := Schur.rowCountLt_eq_rowLen T r
  have h2 := T.1.rowCountLt_mono r hx
  have h3 := T.1.rowCountLt_le_rowLen r x
  omega

theorem rowCount_eq_zero_of_le (T : TauCeti.BoundedSSYT d ν) (r : ℕ) {x : ℕ} (hx : d ≤ x) :
    rowCount T.1 r x = 0 := by
  rw [rowCount, rowCountLt_eq_rowLen_of_le T r hx, rowCountLt_eq_rowLen_of_le T r (by omega),
    Nat.sub_self]

theorem sum_range_rowCount_of_le (T : TauCeti.BoundedSSYT d ν) {N : ℕ} (hN : d ≤ N) (r : ℕ) :
    ∑ l ∈ range N, rowCount T.1 r l = ν.rowLen r := by
  rw [Schur.sum_range_rowCount, rowCountLt_eq_rowLen_of_le T r hN]

theorem sum_range_rowCount_rows (T : TauCeti.BoundedSSYT d ν) {N : ℕ} (hN : ν.colLen 0 ≤ N)
    (l : ℕ) : ∑ r ∈ range N, rowCount T.1 r l = content T.1 l := by
  rw [content_eq_countBelow_of_le T.1 l hN]
  rfl

/-- It suffices to check the lattice condition on the rows `r < d`. -/
theorem isLattice_iff_lt (κ : Weight d) (T : TauCeti.BoundedSSYT d ν) (hν : ν.colLen 0 ≤ d) :
    IsLattice κ T.1 ↔ ∀ r < d, ∀ l, l + 1 < d →
      kap κ (l + 1) + countBelow T.1 (r + 1) (l + 1) ≤ kap κ l + countBelow T.1 r l := by
  constructor
  · intro h r _ l hl
    exact h r l hl
  · intro h
    rw [isLattice_iff_le]
    intro r _ l _ hl
    rcases lt_or_ge r d with hrd | hrd
    · exact h r hrd l hl
    · have h1 := h (d - 1) (by omega) l hl
      rw [show d - 1 + 1 = d by omega] at h1
      have e1 : countBelow T.1 (r + 1) (l + 1) = countBelow T.1 d (l + 1) := by
        rw [countBelow_of_colLen_le _ _ (by omega), countBelow_of_colLen_le _ _ hν]
      have e2 : countBelow T.1 (d - 1) l ≤ countBelow T.1 r l := countBelow_mono _ _ (by omega)
      rw [e1]
      have : (countBelow T.1 (d - 1) l : ℤ) ≤ countBelow T.1 r l := by exact_mod_cast e2
      linarith

theorem runningWeight_apply {m : ℕ} (F : Fin m → VertexFactor)
    (T : (t : Fin m) → TauCeti.BoundedSSYT d (F t).shape) (t : ℕ) (l : Fin d) :
    runningWeight F T t l =
      ∑ t' : Fin m, if (t' : ℕ) < t then (F t').shift + (content (T t').1 l : ℤ) else 0 := by
  rw [runningWeight, Finset.sum_apply]
  refine Finset.sum_congr rfl fun t' _ => ?_
  split_ifs <;> rfl

theorem kap_runningWeight {m : ℕ} (F : Fin m → VertexFactor)
    (T : (t : Fin m) → TauCeti.BoundedSSYT d (F t).shape) (t : ℕ) {l : ℕ} (hl : l < d) :
    kap (runningWeight F T t) l =
      (∑ t' : Fin m, if (t' : ℕ) < t then (F t').shift else 0) +
        ∑ t' : Fin m, if (t' : ℕ) < t then (content (T t').1 l : ℤ) else 0 := by
  rw [kap_of_lt _ hl, runningWeight_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t' _ => ?_
  split_ifs <;> simp

end RowCounts

namespace PositionalQuiver

namespace Realizes

variable {P : PositionalQuiver} {Q : ForwardQuiver} {lam : Q.Weight} (R : P.Realizes Q lam)

/-! ### Slots and the validity predicates of `P` -/

theorem isStart_st (p : Fin Q.s) : P.isStart (R.st p) = true :=
  (R.isStart_iff _ (R.st_lt p)).mpr ⟨p, rfl⟩

theorem slotJ_of_src {p : Fin Q.s} {t : Fin (Q.valence p)} (h : Q.src (Q.arrowAt p t) = p) :
    R.slotJ p t = R.st (Q.tgt (Q.arrowAt p t)) := by
  unfold slotJ otherEnd
  exact ite_eq_left h

theorem slotJ_of_not_src {p : Fin Q.s} {t : Fin (Q.valence p)} (h : Q.src (Q.arrowAt p t) ≠ p) :
    R.slotJ p t = R.st (Q.src (Q.arrowAt p t)) := by
  unfold slotJ otherEnd
  exact ite_eq_right h

theorem slot_valid (p : Fin Q.s) (t : Fin (Q.valence p)) :
    (P.outSlot (R.st p) (R.slotJ p t) (R.slotK p t) ||
      P.inSlot (R.st p) (R.slotJ p t) (R.slotK p t)) = true := by
  rw [R.outSlot_slot, R.inSlot_slot]
  by_cases h : Q.src (Q.arrowAt p t) = p <;> simp [h]

theorem cellOK_slot (p : Fin Q.s) (t : Fin (Q.valence p)) (r l : ℕ) :
    P.cellOK (R.st p) (R.slotJ p t) (R.slotK p t) r l = true ↔ r < Q.dim p ∧ l < Q.dim p := by
  unfold cellOK
  rw [R.isStart_st, R.slot_valid, R.blockDim_st]
  simp

theorem exists_of_cellOK {i j k r l : ℕ} (hi : i < P.n) (hj : j < P.n)
    (h : P.cellOK i j k r l = true) : ∃ p t, R.st p = i ∧ R.slotJ p t = j ∧ R.slotK p t = k := by
  unfold cellOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, -⟩, -⟩ := h
  obtain ⟨p, rfl⟩ := (R.isStart_iff i hi).mp h1
  obtain ⟨t, ht1, ht2⟩ := R.exists_slot p hj h2
  exact ⟨p, t, rfl, ht1, ht2⟩

theorem not_slot_of_invalid {p : Fin Q.s} {j k : ℕ}
    (hv : (P.outSlot (R.st p) j k || P.inSlot (R.st p) j k) = false) (p' : Fin Q.s)
    (t' : Fin (Q.valence p')) : ¬ (R.st p' = R.st p ∧ R.slotJ p' t' = j ∧ R.slotK p' t' = k) := by
  rintro ⟨h1, h2, h3⟩
  have := R.st_injective h1
  subst this
  rw [← h2, ← h3, R.slot_valid] at hv
  exact Bool.noConfusion hv

include R in
theorem ek_lt (e : Q.Arrow) : (e.2 : ℕ) < 2 :=
  lt_of_lt_of_le e.2.isLt (R.arrows_le_two _ _)

theorem shapeOK_arrow (e : Q.Arrow) (r : ℕ) :
    P.shapeOK (R.st (Q.src e)) (R.st (Q.tgt e)) e.2 r =
      decide (r < min (Q.dim (Q.src e)) (Q.dim (Q.tgt e))) := by
  unfold shapeOK
  rw [decide_eq_true (R.lt_arrowCount e), R.blockDim_st, R.blockDim_st, Bool.true_and]

theorem exists_arrow_of_shapeOK {i j k r : ℕ} (hi : i < P.n) (hj : j < P.n)
    (h : P.shapeOK i j k r = true) :
    ∃ e : Q.Arrow, R.st (Q.src e) = i ∧ R.st (Q.tgt e) = j ∧ (e.2 : ℕ) = k := by
  unfold shapeOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hk, -⟩ := h
  obtain ⟨p, q, rfl, rfl⟩ := R.exists_of_arrowCount_ne_zero i hi j hj (by omega)
  rw [R.arrowCount_st] at hk
  exact ⟨⟨(p, q), ⟨k, hk⟩⟩, rfl, rfl, rfl⟩

/-! ### Agreeing coordinates -/

/-- **Coordinates agreeing with arrow shapes and tableaux**: on the index box, the partition
coordinates of each arrow are the rows of its shape, the row-count coordinates of each factor are
the row counts of its tableau, and all other coordinates vanish. -/
structure Agrees (μ : Q.ArrowShapes) (T : Q.Tabs μ) (S : ℕ → ℕ → ℕ → ℕ → ℤ)
    (C : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ) : Prop where
  sh_arrow : ∀ (e : Q.Arrow) (r : ℕ), r < P.n →
    S (R.st (Q.src e)) (R.st (Q.tgt e)) e.2 r = (μ e).1.rowLen r
  sh_zero : ∀ i < P.n, ∀ j < P.n, ∀ k < 2, ∀ r < P.n,
    (∀ e : Q.Arrow, ¬ (R.st (Q.src e) = i ∧ R.st (Q.tgt e) = j ∧ (e.2 : ℕ) = k)) →
      S i j k r = 0
  ce_slot : ∀ (p : Fin Q.s) (t : Fin (Q.valence p)), ∀ r < P.n, ∀ l < P.n,
    C (R.st p) (R.slotJ p t) (R.slotK p t) r l = rowCount (T p t).1 r l
  ce_zero : ∀ i < P.n, ∀ j < P.n, ∀ k < 2, ∀ r < P.n, ∀ l < P.n,
    (∀ (p : Fin Q.s) (t : Fin (Q.valence p)),
      ¬ (R.st p = i ∧ R.slotJ p t = j ∧ R.slotK p t = k)) → C i j k r l = 0

variable {R} {μ : Q.ArrowShapes} {T : Q.Tabs μ} {S : ℕ → ℕ → ℕ → ℕ → ℤ}
  {C : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ}

/-- The row length of the shape of a factor, read in the partition coordinates. -/
theorem rowLength_slot_of
    (hsh : ∀ (e : Q.Arrow) (r : ℕ), r < P.n →
      S (R.st (Q.src e)) (R.st (Q.tgt e)) e.2 r = (μ e).1.rowLen r)
    (p : Fin Q.s) (t : Fin (Q.valence p)) {r : ℕ} (hr : r < Q.dim p) :
    P.rowLength S (R.st p) (R.slotJ p t) (R.slotK p t) r =
      ((Q.vertexFactors μ p t).shape.rowLen r : ℤ) := by
  have hdn := R.dim_le p
  rw [ForwardQuiver.rowLen_vertexFactors μ p t hr]
  unfold rowLength
  rw [R.outSlot_slot]
  by_cases h : Q.src (Q.arrowAt p t) = p
  · rw [decide_eq_true h, ite_eq_left rfl, ite_eq_left h, R.slotJ_of_src h,
      show R.st p = R.st (Q.src (Q.arrowAt p t)) from congrArg R.st h.symm]
    exact hsh (Q.arrowAt p t) r (by omega)
  · rw [decide_eq_false h, ite_eq_right Bool.false_ne_true, ite_eq_right h, R.slotJ_of_not_src h,
      R.blockDim_st, show R.st p = R.st (Q.tgt (Q.arrowAt p t)) from
        congrArg R.st (Q.tgt_eq_of_src_ne h).symm]
    rw [← hsh (Q.arrowAt p t) 0 (by omega), ← hsh (Q.arrowAt p t) (Q.dim p - 1 - r) (by omega)]
    rfl

namespace Agrees

variable (hA : R.Agrees μ T S C)
include hA

theorem shapeCond {i j k r : ℕ} (hi : i < P.n) (hj : j < P.n) (hk : k < 2) (hr : r < P.n) :
    P.ShapeCond S i j k r := by
  unfold ShapeCond
  by_cases hex : ∃ e : Q.Arrow, R.st (Q.src e) = i ∧ R.st (Q.tgt e) = j ∧ (e.2 : ℕ) = k
  · obtain ⟨e, rfl, rfl, rfl⟩ := hex
    rw [R.shapeOK_arrow, R.shapeOK_arrow]
    simp only [decide_eq_true_eq]
    have hmn : min (Q.dim (Q.src e)) (Q.dim (Q.tgt e)) ≤ P.n :=
      (min_le_left _ _).trans (R.dim_le _)
    split_ifs with h1
    · refine ⟨by rw [hA.sh_arrow e r hr]; exact Nat.cast_nonneg _, fun h2 => ?_⟩
      rw [hA.sh_arrow e r hr, hA.sh_arrow e (r + 1) (by omega)]
      exact_mod_cast (μ e).1.rowLen_anti r (r + 1) (Nat.le_succ r)
    · rw [hA.sh_arrow e r hr, YoungDiagram.rowLen_eq_zero_of_colLen_le ((μ e).2.trans
        (not_lt.mp h1)), Nat.cast_zero]
  · have hS0 := hA.sh_zero i hi j hj k hk r hr fun e he => hex ⟨e, he⟩
    have hok : P.shapeOK i j k r = false := by
      cases h : P.shapeOK i j k r
      · rfl
      · exact absurd (R.exists_arrow_of_shapeOK hi hj h) hex
    rw [hok]
    simpa using hS0

theorem cellCond {i j k r l : ℕ} (hi : i < P.n) (hj : j < P.n) (hk : k < 2) (hr : r < P.n)
    (hl : l < P.n) : P.CellCond C i j k r l := by
  unfold CellCond
  by_cases hex : ∃ (p : Fin Q.s) (t : Fin (Q.valence p)),
      R.st p = i ∧ R.slotJ p t = j ∧ R.slotK p t = k
  · obtain ⟨p, t, rfl, rfl, rfl⟩ := hex
    rw [hA.ce_slot p t r hr l hl]
    split_ifs with h
    · exact Nat.cast_nonneg _
    · rw [R.cellOK_slot] at h
      rcases not_and_or.mp h with h1 | h1
      · rw [rowCount_eq_zero_of_colLen_le _
          ((ForwardQuiver.colLen_vertexFactors μ p t).trans (not_lt.mp h1)), Nat.cast_zero]
      · rw [rowCount_eq_zero_of_le _ r (not_lt.mp h1), Nat.cast_zero]
  · have h0 := hA.ce_zero i hi j hj k hk r hr l hl fun p t h => hex ⟨p, t, h⟩
    rw [h0]
    split_ifs <;> simp

theorem rowSumCond {i j k r : ℕ} (hi : i < P.n) (hj : j < P.n) (hr : r < P.n) :
    P.RowSumCond S C i j k r := by
  intro h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  obtain ⟨p, rfl⟩ := (R.isStart_iff i hi).mp h1
  obtain ⟨t, rfl, rfl⟩ := R.exists_slot p hj h2
  rw [R.blockDim_st] at h3
  rw [rowLength_slot_of hA.sh_arrow p t h3,
    Finset.sum_congr rfl fun l hl => hA.ce_slot p t r hr l (mem_range.mp hl), ← Nat.cast_sum,
    sum_range_rowCount_of_le _ (R.dim_le p)]

theorem columnCond {i j k r l : ℕ} (hi : i < P.n) (hj : j < P.n) :
    P.ColumnCond C i j k r l := by
  intro h
  obtain ⟨p, t, rfl, rfl, rfl⟩ := R.exists_of_cellOK hi hj h
  rw [R.cellOK_slot] at h
  obtain ⟨h1, h2⟩ := h
  have hdn := R.dim_le p
  rw [Finset.sum_congr rfl fun l' hl' =>
      hA.ce_slot p t (r + 1) (by omega) l' (by rw [mem_range] at hl'; omega),
    Finset.sum_congr rfl fun l' hl' =>
      hA.ce_slot p t r (by omega) l' (by rw [mem_range] at hl'; omega),
    ← Nat.cast_sum, ← Nat.cast_sum, Schur.sum_range_rowCount, Schur.sum_range_rowCount]
  exact_mod_cast (T p t).1.rowCountLt_succ_le r l

theorem sum_ce_rows (p : Fin Q.s) (t : Fin (Q.valence p)) {N l : ℕ} (hN : N ≤ P.n)
    (hl : l < P.n) :
    ∑ r' ∈ range N, C (R.st p) (R.slotJ p t) (R.slotK p t) r' l =
      (countBelow (T p t).1 N l : ℤ) := by
  rw [Finset.sum_congr rfl fun r' hr' => hA.ce_slot p t r' (by rw [mem_range] at hr'; omega) l hl,
    countBelow, Nat.cast_sum]

theorem content_eq_sum_ce (p : Fin Q.s) (t : Fin (Q.valence p)) {l : ℕ} (hl : l < P.n) :
    ∑ r' ∈ range P.n, C (R.st p) (R.slotJ p t) (R.slotK p t) r' l =
      (content (T p t).1 l : ℤ) := by
  rw [hA.sum_ce_rows p t le_rfl hl, ← content_eq_countBelow_of_le]
  exact (ForwardQuiver.colLen_vertexFactors μ p t).trans (R.dim_le p)

/-- The entries `l` of the tableaux before a factor, read in the row-count coordinates. -/
theorem before_slot (p : Fin Q.s) (t : Fin (Q.valence p)) {l : ℕ} (hl : l < P.n) :
    P.before C (R.st p) (R.slotJ p t) (R.slotK p t) l =
      ∑ t' : Fin (Q.valence p), if (t' : ℕ) < t then (content (T p t').1 l : ℤ) else 0 := by
  unfold before
  rw [R.sum_slots p (fun j' k' => if P.slotBefore (R.st p) j' k' (R.slotJ p t) (R.slotK p t)
    then ∑ r' ∈ range P.n, C (R.st p) j' k' r' l else 0)]
  · refine Finset.sum_congr rfl fun t' _ => ?_
    by_cases h : t' < t
    · rw [ite_eq_left ((R.lt_iff_slotBefore p t t').mp h), ite_eq_left (show (t' : ℕ) < t from h),
        hA.content_eq_sum_ce p t' hl]
    · rw [ite_eq_right fun h' => h ((R.lt_iff_slotBefore p t t').mpr h'),
        ite_eq_right (show ¬ (t' : ℕ) < t from h)]
  · intro j' hj' k' hk' hv
    split_ifs
    · exact Finset.sum_eq_zero fun r' hr' =>
        hA.ce_zero _ (R.st_lt p) j' hj' k' hk' r' (mem_range.mp hr') l hl
          (R.not_slot_of_invalid hv)
    · rfl

/-- All entries `l` of the tableaux at a vertex, read in the row-count coordinates. -/
theorem total_st (p : Fin Q.s) {l : ℕ} (hl : l < P.n) :
    P.total C (R.st p) l = ∑ t : Fin (Q.valence p), (content (T p t).1 l : ℤ) := by
  unfold total
  rw [R.sum_slots p (fun j' k' => ∑ r' ∈ range P.n, C (R.st p) j' k' r' l)]
  · exact Finset.sum_congr rfl fun t _ => hA.content_eq_sum_ce p t hl
  · intro j' hj' k' hk' hv
    exact Finset.sum_eq_zero fun r' hr' =>
      hA.ce_zero _ (R.st_lt p) j' hj' k' hk' r' (mem_range.mp hr') l hl
        (R.not_slot_of_invalid hv)

/-- The shifts `μ_{e,0}` of the arrows into a vertex, read in the partition coordinates. -/
theorem inShift_st (p : Fin Q.s) :
    P.inShift S (R.st p) = ∑ t : Fin (Q.valence p),
      if Q.src (Q.arrowAt p t) = p then 0 else ((μ (Q.arrowAt p t)).1.rowLen 0 : ℤ) := by
  unfold inShift
  rw [R.sum_slots p (fun j k => if k < P.arrowCount j (R.st p) then S j (R.st p) k 0 else 0)]
  · refine Finset.sum_congr rfl fun t _ => ?_
    have hin := R.inSlot_slot p t
    unfold inSlot at hin
    by_cases h : Q.src (Q.arrowAt p t) = p
    · rw [ite_eq_right (by simpa [h] using hin), ite_eq_left h]
    · rw [ite_eq_left (by simpa [h] using hin), ite_eq_right h, R.slotJ_of_not_src h,
        show R.st p = R.st (Q.tgt (Q.arrowAt p t)) from
          congrArg R.st (Q.tgt_eq_of_src_ne h).symm]
      exact hA.sh_arrow (Q.arrowAt p t) 0 (by have := R.st_lt (Q.tgt (Q.arrowAt p t)); omega)
  · intro j _ k _ hv
    rw [Bool.or_eq_false_iff] at hv
    unfold inSlot at hv
    exact ite_eq_right (by simpa using hv.2)

/-! ### Families 5 and 6 -/

/-- **The lattice condition of a factor** is family 5 at its slot. -/
theorem isLattice_iff (p : Fin Q.s) (t : Fin (Q.valence p)) :
    IsLattice (runningWeight (Q.vertexFactors μ p) (T p) t) (T p t).1 ↔
      ∀ r < P.n, ∀ l < P.n, P.LatticeCond C (R.st p) (R.slotJ p t) (R.slotK p t) r l := by
  have hdn := R.dim_le p
  rw [isLattice_iff_lt _ _ (ForwardQuiver.colLen_vertexFactors μ p t)]
  constructor
  · intro h r hr l hl hok
    rw [R.cellOK_slot] at hok
    obtain ⟨hrd, hld⟩ := hok
    have h1 := h r hrd l hld
    rw [kap_runningWeight _ _ _ hld, kap_runningWeight _ _ _ (by omega)] at h1
    rw [hA.before_slot p t (by omega), hA.before_slot p t hl, hA.sum_ce_rows p t (by omega) hl,
      hA.sum_ce_rows p t (by omega) (by omega)]
    linarith
  · intro h r hrd l hld
    have h1 := h r (by omega) l (by omega) ((R.cellOK_slot p t r (l + 1)).mpr ⟨hrd, hld⟩)
    rw [hA.before_slot p t (by omega), hA.before_slot p t (by omega),
      hA.sum_ce_rows p t (by omega) (by omega), hA.sum_ce_rows p t (by omega) (by omega)] at h1
    rw [kap_runningWeight _ _ _ hld, kap_runningWeight _ _ _ (by omega)]
    linarith

theorem latticeConds_iff :
    (∀ i < P.n, ∀ j < P.n, ∀ k < 2, ∀ r < P.n, ∀ l < P.n, P.LatticeCond C i j k r l) ↔
      ∀ (p : Fin Q.s) (t : Fin (Q.valence p)),
        IsLattice (runningWeight (Q.vertexFactors μ p) (T p) t) (T p t).1 := by
  constructor
  · intro h p t
    rw [hA.isLattice_iff]
    intro r hr l hl
    exact h _ (R.st_lt p) _ (R.slotJ_lt p t) _ (R.slotK_lt p t) r hr l hl
  · intro h i hi j hj k _ r hr l hl hok
    obtain ⟨p, t, rfl, rfl, rfl⟩ := R.exists_of_cellOK hi hj hok
    exact (hA.isLattice_iff p t).mp (h p t) r hr l hl hok

theorem runningWeight_last (p : Fin Q.s) {l : ℕ} (hl : l < Q.dim p) :
    runningWeight (Q.vertexFactors μ p) (T p) (Q.valence p) ⟨l, hl⟩ =
      -P.inShift S (R.st p) + P.total C (R.st p) l := by
  have hdn := R.dim_le p
  rw [runningWeight_apply, hA.inShift_st, hA.total_st p (by omega), ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [ite_eq_left t.isLt, ForwardQuiver.shift_vertexFactors]
  split_ifs <;> simp

/-- **The final weight at a vertex** is family 6 there. -/
theorem final_iff (p : Fin Q.s) :
    runningWeight (Q.vertexFactors μ p) (T p) (Q.valence p) = lam p ↔
      ∀ l < P.n, P.FinalCond S C (R.st p) l := by
  constructor
  · intro h l _ hpre
    simp only [R.isStart_st, R.blockDim_st, Bool.true_and, decide_eq_true_eq] at hpre
    rw [← hA.runningWeight_last p hpre, h,
      (R.weight_st p ⟨l, hpre⟩ : P.weight (R.st p) l = lam p ⟨l, hpre⟩), Int.cast_id]
  · intro h
    funext l
    have hdn := R.dim_le p
    have h1 := h l (by omega) (by simp [R.isStart_st, R.blockDim_st, l.isLt])
    rw [hA.runningWeight_last p l.isLt, h1, Int.cast_id]
    exact R.weight_st p l

theorem finalConds_iff :
    (∀ i < P.n, ∀ l < P.n, P.FinalCond S C i l) ↔
      ∀ p : Fin Q.s, runningWeight (Q.vertexFactors μ p) (T p) (Q.valence p) = lam p := by
  constructor
  · intro h p
    exact (hA.final_iff p).mpr fun l hl => h _ (R.st_lt p) l hl
  · intro h i hi l hl hpre
    have h1 : P.isStart i = true := by
      simp only [Bool.and_eq_true] at hpre
      exact hpre.1
    obtain ⟨p, rfl⟩ := (R.isStart_iff i hi).mp h1
    exact (hA.final_iff p).mp (h p) l hl hpre

/-- **The conditions of the polytope are the conditions of LR chains**: for coordinates agreeing
with `(μ, T)`, the six families hold exactly when every `T p` is an LR chain for the factors at
`p` ending at `λ^{(p)}`. -/
theorem conditions_iff :
    P.Conditions S C ↔ ∀ p : Fin Q.s, IsLRChain (Q.vertexFactors μ p) (lam p) (T p) := by
  constructor
  · rintro ⟨-, -, -, -, h5, h6⟩ p
    exact ⟨(hA.latticeConds_iff.mp h5) p, (hA.finalConds_iff.mp h6) p⟩
  · intro h
    exact ⟨fun i hi j hj k hk r hr => hA.shapeCond hi hj hk hr,
      fun i hi j hj k hk r hr l hl => hA.cellCond hi hj hk hr hl,
      fun i hi j hj _ _ r hr => hA.rowSumCond hi hj hr,
      fun i hi j hj _ _ _ _ _ _ => hA.columnCond hi hj,
      hA.latticeConds_iff.mpr fun p => (h p).1,
      hA.finalConds_iff.mpr fun p => (h p).2⟩

end Agrees

end Realizes

end PositionalQuiver

end Flat

end Schubert.RS.Quiver
