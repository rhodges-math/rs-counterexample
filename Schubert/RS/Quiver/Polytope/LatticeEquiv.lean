import Schubert.RS.Quiver.Polytope.LatticeChains

/-!
# Points of the polytope and LR chains

Let positional data `P` realize a forward quiver `Q` with weight `λ`. The points of `P` with
integer coordinates satisfying the six families of conditions
(`Schubert.RS.Quiver.Flat.PositionalQuiver.Conditions`) are in bijection with the pairs `(μ, T)` of
arrow shapes and LR chains at the vertices, `Σ μ, Q.VertexChains μ λ`
(`Schubert.RS.Quiver.Flat.PositionalQuiver.Realizes.conditionsEquiv`).

* The point of `(μ, T)` (`Schubert.RS.Quiver.Flat.PositionalQuiver.Realizes.encode`) has the rows
  of `μ_e` as the partition coordinates of the arrow `e` and the row counts of `T p t` as the
  row-count coordinates of the factor `t` at `p`, and `0` elsewhere.
* Conversely, the partition coordinates of a point satisfying the conditions are weakly decreasing
  and nonnegative, so they are the rows of Young diagrams
  (`Schubert.RS.Quiver.Flat.PositionalQuiver.Realizes.shapesOf`); its row-count coordinates satisfy
  the row-count constraints, so they are the row counts of tableaux
  (`Schubert.RS.Quiver.Flat.PositionalQuiver.Realizes.tabsOf`, through
  `Schubert.RS.Quiver.Schur.rowCountsEquiv`). These agree with the point, so they form LR chains
  (`Schubert.RS.Quiver.Flat.PositionalQuiver.Realizes.Agrees.conditions_iff`).

## Main definitions

* `Schubert.RS.Quiver.Flat.PositionalQuiver.Realizes.encode`
* `Schubert.RS.Quiver.Flat.PositionalQuiver.Realizes.shapesOf`,
  `Schubert.RS.Quiver.Flat.PositionalQuiver.Realizes.tabsOf`
* `Schubert.RS.Quiver.Flat.PositionalQuiver.Realizes.conditionsEquiv`
-/

namespace Schubert.RS.Quiver

open Finset SemistandardYoungTableau Schubert.RS.LR Schubert.RS.Quiver.Schur

namespace ForwardQuiver

variable {Q : ForwardQuiver}

theorem arrow_ext {e e' : Q.Arrow} (h1 : Q.src e' = Q.src e) (h2 : Q.tgt e' = Q.tgt e)
    (h3 : (e'.2 : ℕ) = e.2) : e' = e := by
  obtain ⟨⟨a, b⟩, k⟩ := e
  obtain ⟨⟨a', b'⟩, k'⟩ := e'
  simp only [src, tgt] at h1 h2
  subst h1 h2
  simp only at h3
  rw [Fin.ext h3]

end ForwardQuiver

theorem youngDiagram_ext_rowLen {μ ν : YoungDiagram} (h : ∀ r, μ.rowLen r = ν.rowLen r) :
    μ = ν := by
  refine YoungDiagram.ext (Finset.ext fun c => ?_)
  obtain ⟨i, j⟩ := c
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen,
    YoungDiagram.mem_iff_lt_rowLen, h]

namespace Flat

namespace PositionalQuiver

namespace Realizes

noncomputable section

variable {P : PositionalQuiver} {Q : ForwardQuiver} {lam : Q.Weight} (R : P.Realizes Q lam)

/-! ### The point of arrow shapes and tableaux -/

/-- The partition coordinates of arrow shapes. -/
def shEnc (μ : Q.ArrowShapes) (i j k r : ℕ) : ℤ :=
  ∑ e : Q.Arrow, if R.st (Q.src e) = i ∧ R.st (Q.tgt e) = j ∧ (e.2 : ℕ) = k then
    ((μ e).1.rowLen r : ℤ) else 0

/-- The row-count coordinates of tableaux. -/
def ceEnc (μ : Q.ArrowShapes) (T : Q.Tabs μ) (i j k r l : ℕ) : ℤ :=
  ∑ p : Fin Q.s, ∑ t : Fin (Q.valence p),
    if R.st p = i ∧ R.slotJ p t = j ∧ R.slotK p t = k then (rowCount (T p t).1 r l : ℤ) else 0

/-- **The point of arrow shapes and tableaux.** -/
def encode (μ : Q.ArrowShapes) (T : Q.Tabs μ) : Fin P.dim → ℤ :=
  P.ofCoords (R.shEnc μ) (R.ceEnc μ T)

theorem shEnc_arrow (μ : Q.ArrowShapes) (e : Q.Arrow) (r : ℕ) :
    R.shEnc μ (R.st (Q.src e)) (R.st (Q.tgt e)) e.2 r = (μ e).1.rowLen r := by
  unfold shEnc
  rw [Fintype.sum_eq_single e]
  · exact ite_eq_left ⟨rfl, rfl, rfl⟩
  · intro e' he'
    exact ite_eq_right fun h =>
      he' (ForwardQuiver.arrow_ext (R.st_injective h.1) (R.st_injective h.2.1) h.2.2)

theorem shEnc_eq_zero (μ : Q.ArrowShapes) {i j k : ℕ}
    (h : ∀ e : Q.Arrow, ¬ (R.st (Q.src e) = i ∧ R.st (Q.tgt e) = j ∧ (e.2 : ℕ) = k)) (r : ℕ) :
    R.shEnc μ i j k r = 0 :=
  Finset.sum_eq_zero fun e _ => ite_eq_right (h e)

theorem ceEnc_slot (μ : Q.ArrowShapes) (T : Q.Tabs μ) (p : Fin Q.s) (t : Fin (Q.valence p))
    (r l : ℕ) : R.ceEnc μ T (R.st p) (R.slotJ p t) (R.slotK p t) r l = rowCount (T p t).1 r l := by
  unfold ceEnc
  rw [Fintype.sum_eq_single p, Fintype.sum_eq_single t]
  · exact ite_eq_left ⟨rfl, rfl, rfl⟩
  · intro t' ht'
    exact ite_eq_right fun h => ht' (R.slot_injective p h.2.1 h.2.2)
  · intro p' hp'
    exact Finset.sum_eq_zero fun t' _ => ite_eq_right fun h => hp' (R.st_injective h.1)

theorem ceEnc_eq_zero (μ : Q.ArrowShapes) (T : Q.Tabs μ) {i j k : ℕ}
    (h : ∀ (p : Fin Q.s) (t : Fin (Q.valence p)),
      ¬ (R.st p = i ∧ R.slotJ p t = j ∧ R.slotK p t = k)) (r l : ℕ) :
    R.ceEnc μ T i j k r l = 0 :=
  Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun t _ => ite_eq_right (h p t)

/-- The point of `(μ, T)` agrees with `(μ, T)`. -/
theorem agrees_encode (μ : Q.ArrowShapes) (T : Q.Tabs μ) :
    R.Agrees μ T (P.sh (R.encode μ T)) (P.ce (R.encode μ T)) where
  sh_arrow e r hr := by
    rw [encode, P.sh_ofCoords _ _ (R.st_lt _) (R.st_lt _) (R.ek_lt e) hr, R.shEnc_arrow]
  sh_zero i hi j hj k hk r hr h := by
    rw [encode, P.sh_ofCoords _ _ hi hj hk hr, R.shEnc_eq_zero μ h]
  ce_slot p t r hr l hl := by
    rw [encode, P.ce_ofCoords _ _ (R.st_lt p) (R.slotJ_lt p t) (R.slotK_lt p t) hr hl,
      R.ceEnc_slot]
  ce_zero i hi j hj k hk r hr l hl h := by
    rw [encode, P.ce_ofCoords _ _ hi hj hk hr hl, R.ceEnc_eq_zero μ T h]

/-! ### Arrow shapes and tableaux of a point -/

variable {S : ℕ → ℕ → ℕ → ℕ → ℤ} {C : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ}

/-- The rows of the partition of an arrow, read in the partition coordinates. -/
def shapeSeq (S : ℕ → ℕ → ℕ → ℕ → ℤ) (e : Q.Arrow) (r : ℕ) : ℕ :=
  (S (R.st (Q.src e)) (R.st (Q.tgt e)) e.2 r).toNat

/-- The row counts of the factor `t` at `p`, read in the row-count coordinates. -/
def cOf (C : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ) (p : Fin Q.s) (t : Fin (Q.valence p))
    (r l : Fin (Q.dim p)) : ℕ :=
  (C (R.st p) (R.slotJ p t) (R.slotK p t) r l).toNat

section Shapes

variable (hx : P.Conditions S C)
include hx

theorem shapeCond_arrow (e : Q.Arrow) {r : ℕ} (hr : r < P.n) :
    if r < min (Q.dim (Q.src e)) (Q.dim (Q.tgt e)) then
      0 ≤ S (R.st (Q.src e)) (R.st (Q.tgt e)) e.2 r ∧
        (r + 1 < min (Q.dim (Q.src e)) (Q.dim (Q.tgt e)) →
          S (R.st (Q.src e)) (R.st (Q.tgt e)) e.2 (r + 1) ≤
            S (R.st (Q.src e)) (R.st (Q.tgt e)) e.2 r)
    else S (R.st (Q.src e)) (R.st (Q.tgt e)) e.2 r = 0 := by
  have h := hx.1 (R.st (Q.src e)) (R.st_lt _) (R.st (Q.tgt e)) (R.st_lt _) e.2 (R.ek_lt e) r hr
  unfold ShapeCond at h
  rw [R.shapeOK_arrow, R.shapeOK_arrow] at h
  simpa only [decide_eq_true_eq] using h

theorem sh_nonneg (e : Q.Arrow) {r : ℕ} (hr : r < min (Q.dim (Q.src e)) (Q.dim (Q.tgt e))) :
    0 ≤ S (R.st (Q.src e)) (R.st (Q.tgt e)) e.2 r := by
  have hn : min (Q.dim (Q.src e)) (Q.dim (Q.tgt e)) ≤ P.n := (min_le_left _ _).trans (R.dim_le _)
  have h := R.shapeCond_arrow hx e (r := r) (by omega)
  rw [ite_eq_left hr] at h
  exact h.1

theorem sh_succ_le (e : Q.Arrow) {r : ℕ}
    (hr : r + 1 < min (Q.dim (Q.src e)) (Q.dim (Q.tgt e))) :
    S (R.st (Q.src e)) (R.st (Q.tgt e)) e.2 (r + 1) ≤
      S (R.st (Q.src e)) (R.st (Q.tgt e)) e.2 r := by
  have hn : min (Q.dim (Q.src e)) (Q.dim (Q.tgt e)) ≤ P.n := (min_le_left _ _).trans (R.dim_le _)
  have h := R.shapeCond_arrow hx e (r := r) (by omega)
  rw [ite_eq_left (by omega)] at h
  exact h.2 hr

theorem sh_eq_zero_of_le (e : Q.Arrow) {r : ℕ}
    (hr : min (Q.dim (Q.src e)) (Q.dim (Q.tgt e)) ≤ r) (hrn : r < P.n) :
    S (R.st (Q.src e)) (R.st (Q.tgt e)) e.2 r = 0 := by
  have h := R.shapeCond_arrow hx e hrn
  rw [ite_eq_right (by omega)] at h
  exact h

theorem sh_zero_of_not_arrow {i j k r : ℕ} (hi : i < P.n) (hj : j < P.n) (hk : k < 2)
    (hr : r < P.n)
    (h : ∀ e : Q.Arrow, ¬ (R.st (Q.src e) = i ∧ R.st (Q.tgt e) = j ∧ (e.2 : ℕ) = k)) :
    S i j k r = 0 := by
  have hc := hx.1 i hi j hj k hk r hr
  have hok : P.shapeOK i j k r = false := by
    cases hs : P.shapeOK i j k r
    · rfl
    · obtain ⟨e, he⟩ := R.exists_arrow_of_shapeOK hi hj hs
      exact absurd he (h e)
  unfold ShapeCond at hc
  rw [hok] at hc
  simpa using hc

omit hx in
theorem shapeSeq_antitone_of {e : Q.Arrow}
    (hstep : ∀ r, r + 1 < min (Q.dim (Q.src e)) (Q.dim (Q.tgt e)) →
      R.shapeSeq S e (r + 1) ≤ R.shapeSeq S e r) :
    Antitone fun r : Fin (min (Q.dim (Q.src e)) (Q.dim (Q.tgt e))) => R.shapeSeq S e r := by
  intro a b hab
  have key : ∀ b' : ℕ, (a : ℕ) ≤ b' → b' < min (Q.dim (Q.src e)) (Q.dim (Q.tgt e)) →
      R.shapeSeq S e b' ≤ R.shapeSeq S e a := by
    intro b' hab'
    induction b', hab' using Nat.le_induction with
    | base => exact fun _ => le_rfl
    | succ b' _ ih => exact fun hb => (hstep b' hb).trans (ih (by omega))
  exact key b hab b.isLt

theorem shapeSeq_antitone (e : Q.Arrow) :
    Antitone fun r : Fin (min (Q.dim (Q.src e)) (Q.dim (Q.tgt e))) => R.shapeSeq S e r :=
  R.shapeSeq_antitone_of fun _ hr => Int.toNat_le_toNat (R.sh_succ_le hx e hr)

/-- **The arrow shapes of a point**: the partition coordinates of each arrow are the rows of a
Young diagram. -/
def shapesOf : Q.ArrowShapes := fun e =>
  ⟨YoungDiagram.ofRowLensFin _ (R.shapeSeq_antitone hx e),
    YoungDiagram.colLen_zero_ofRowLensFin_le _ _⟩

theorem rowLen_shapesOf (e : Q.Arrow) {r : ℕ} (hr : r < P.n) :
    ((R.shapesOf hx e).1.rowLen r : ℤ) = S (R.st (Q.src e)) (R.st (Q.tgt e)) e.2 r := by
  change ((YoungDiagram.ofRowLensFin _ (R.shapeSeq_antitone hx e)).rowLen r : ℤ) = _
  by_cases h : r < min (Q.dim (Q.src e)) (Q.dim (Q.tgt e))
  · have := YoungDiagram.rowLen_ofRowLensFin _ (R.shapeSeq_antitone hx e) ⟨r, h⟩
    simp only at this
    rw [this, shapeSeq, Int.toNat_of_nonneg (R.sh_nonneg hx e h)]
  · rw [YoungDiagram.rowLen_ofRowLensFin_eq_zero_of_le _ _ (not_lt.mp h), Nat.cast_zero,
      R.sh_eq_zero_of_le hx e (not_lt.mp h) hr]

end Shapes

section Tableaux

variable (hx : P.Conditions S C)
include hx

theorem ce_nonneg (p : Fin Q.s) (t : Fin (Q.valence p)) {r l : ℕ} (hr : r < Q.dim p)
    (hl : l < Q.dim p) : 0 ≤ C (R.st p) (R.slotJ p t) (R.slotK p t) r l := by
  have hdn := R.dim_le p
  have h := hx.2.1 _ (R.st_lt p) _ (R.slotJ_lt p t) _ (R.slotK_lt p t) r (by omega) l (by omega)
  unfold CellCond at h
  rw [ite_eq_left ((R.cellOK_slot p t r l).mpr ⟨hr, hl⟩)] at h
  exact h

theorem ce_eq_zero_of_not_lt (p : Fin Q.s) (t : Fin (Q.valence p)) {r l : ℕ} (hr : r < P.n)
    (hl : l < P.n) (h : ¬ (r < Q.dim p ∧ l < Q.dim p)) :
    C (R.st p) (R.slotJ p t) (R.slotK p t) r l = 0 := by
  have hc := hx.2.1 _ (R.st_lt p) _ (R.slotJ_lt p t) _ (R.slotK_lt p t) r hr l hl
  unfold CellCond at hc
  rw [ite_eq_right fun h' => h ((R.cellOK_slot p t r l).mp h')] at hc
  exact hc

theorem ce_zero_of_not_slot {i j k r l : ℕ} (hi : i < P.n) (hj : j < P.n) (hk : k < 2)
    (hr : r < P.n) (hl : l < P.n)
    (h : ∀ (p : Fin Q.s) (t : Fin (Q.valence p)),
      ¬ (R.st p = i ∧ R.slotJ p t = j ∧ R.slotK p t = k)) : C i j k r l = 0 := by
  have hc := hx.2.1 i hi j hj k hk r hr l hl
  have hok : P.cellOK i j k r l = false := by
    cases hs : P.cellOK i j k r l
    · rfl
    · obtain ⟨p, t, h'⟩ := R.exists_of_cellOK hi hj hs
      exact absurd h' (h p t)
  unfold CellCond at hc
  rw [hok] at hc
  simpa using hc

theorem cOf_cast (p : Fin Q.s) (t : Fin (Q.valence p)) (r l : Fin (Q.dim p)) :
    (R.cOf C p t r l : ℤ) = C (R.st p) (R.slotJ p t) (R.slotK p t) r l :=
  Int.toNat_of_nonneg (R.ce_nonneg hx p t r.isLt l.isLt)

/-- The row-count coordinates of each factor satisfy the row-count constraints of its shape. -/
theorem rowCountConstraints_cOf (p : Fin Q.s) (t : Fin (Q.valence p)) :
    RowCountConstraints (Q.vertexFactors (R.shapesOf hx) p t).shape (R.cOf C p t) := by
  have hdn := R.dim_le p
  refine ⟨fun r => ?_, fun r hr k => ?_⟩
  · have h := hx.2.2.1 _ (R.st_lt p) _ (R.slotJ_lt p t) _ (R.slotK_lt p t) r (by omega)
      (by rw [R.isStart_st, R.slot_valid, R.blockDim_st]; simp [r.isLt])
    rw [rowLength_slot_of (fun e r hr => (R.rowLen_shapesOf hx e hr).symm) p t r.isLt] at h
    have h2 : ∑ l ∈ range P.n, C (R.st p) (R.slotJ p t) (R.slotK p t) r l =
        ∑ l : Fin (Q.dim p), (R.cOf C p t r l : ℤ) := by
      rw [sum_fin_eq_sum_range (fun l => (R.cOf C p t r l : ℤ))
        (fun l => C (R.st p) (R.slotJ p t) (R.slotK p t) r l) fun l => R.cOf_cast hx p t r l]
      exact (Finset.sum_subset (range_mono hdn) fun l hl hl' =>
        R.ce_eq_zero_of_not_lt hx p t (by omega) (mem_range.mp hl)
          fun h' => hl' (mem_range.mpr h'.2)).symm
    rw [h2, ← Nat.cast_sum] at h
    exact_mod_cast h
  · have h := hx.2.2.2.1 _ (R.st_lt p) _ (R.slotJ_lt p t) _ (R.slotK_lt p t) r (by omega) k
      (by omega) ((R.cellOK_slot p t (r + 1) k).mpr ⟨hr, k.isLt⟩)
    rw [← sum_fin_filter_le (fun k' => (R.cOf C p t ⟨r + 1, hr⟩ k' : ℤ))
        (fun l' => C (R.st p) (R.slotJ p t) (R.slotK p t) (r + 1) l')
        (fun k' => R.cOf_cast hx p t _ k'),
      ← sum_fin_filter_lt (fun k' => (R.cOf C p t ⟨r, by omega⟩ k' : ℤ))
        (fun l' => C (R.st p) (R.slotJ p t) (R.slotK p t) r l')
        (fun k' => R.cOf_cast hx p t _ k')] at h
    exact_mod_cast h

/-- **The tableaux of a point**: the tableaux with its row-count coordinates as row counts. -/
def tabsOf : Q.Tabs (R.shapesOf hx) := fun p t =>
  (rowCountsEquiv _ (ForwardQuiver.colLen_vertexFactors _ p t)).symm
    ⟨R.cOf C p t, R.rowCountConstraints_cOf hx p t⟩

theorem rowCount_tabsOf (p : Fin Q.s) (t : Fin (Q.valence p)) {r l : ℕ} (hr : r < Q.dim p)
    (hl : l < Q.dim p) : rowCount (R.tabsOf hx p t).1 r l = R.cOf C p t ⟨r, hr⟩ ⟨l, hl⟩ := by
  have e1 := (rowCountsEquiv _
    (ForwardQuiver.colLen_vertexFactors (R.shapesOf hx) p t)).apply_symm_apply
      ⟨R.cOf C p t, R.rowCountConstraints_cOf hx p t⟩
  exact congrArg (fun z => z.1 ⟨r, hr⟩ ⟨l, hl⟩) e1

/-- The arrow shapes and tableaux of a point agree with it. -/
theorem agrees_of : R.Agrees (R.shapesOf hx) (R.tabsOf hx) S C where
  sh_arrow e r hr := (R.rowLen_shapesOf hx e hr).symm
  sh_zero i hi j hj k hk r hr h := R.sh_zero_of_not_arrow hx hi hj hk hr h
  ce_slot p t r hr l hl := by
    by_cases h : r < Q.dim p ∧ l < Q.dim p
    · rw [R.rowCount_tabsOf hx p t h.1 h.2, R.cOf_cast hx]
    · rw [R.ce_eq_zero_of_not_lt hx p t hr hl h]
      rcases not_and_or.mp h with h1 | h1
      · rw [rowCount_eq_zero_of_colLen_le _
          ((ForwardQuiver.colLen_vertexFactors _ p t).trans (not_lt.mp h1)), Nat.cast_zero]
      · rw [rowCount_eq_zero_of_le _ r (not_lt.mp h1), Nat.cast_zero]
  ce_zero i hi j hj k hk r hr l hl h := R.ce_zero_of_not_slot hx hi hj hk hr hl h

end Tableaux

/-! ### Uniqueness -/

namespace Agrees

variable {R} {μ μ' : Q.ArrowShapes} {T : Q.Tabs μ} {T' : Q.Tabs μ'}
  {S' : ℕ → ℕ → ℕ → ℕ → ℤ} {C' : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ}

theorem sh_eq {T'' : Q.Tabs μ} (hA : R.Agrees μ T S C) (hA' : R.Agrees μ T'' S' C')
    {i j k r : ℕ} (hi : i < P.n) (hj : j < P.n) (hk : k < 2) (hr : r < P.n) :
    S i j k r = S' i j k r := by
  by_cases hex : ∃ e : Q.Arrow, R.st (Q.src e) = i ∧ R.st (Q.tgt e) = j ∧ (e.2 : ℕ) = k
  · obtain ⟨e, rfl, rfl, rfl⟩ := hex
    rw [hA.sh_arrow e r hr, hA'.sh_arrow e r hr]
  · rw [hA.sh_zero i hi j hj k hk r hr fun e he => hex ⟨e, he⟩,
      hA'.sh_zero i hi j hj k hk r hr fun e he => hex ⟨e, he⟩]

theorem ce_eq (hA : R.Agrees μ T S C) (hA' : R.Agrees μ T S' C') {i j k r l : ℕ}
    (hi : i < P.n) (hj : j < P.n) (hk : k < 2) (hr : r < P.n) (hl : l < P.n) :
    C i j k r l = C' i j k r l := by
  by_cases hex : ∃ (p : Fin Q.s) (t : Fin (Q.valence p)),
      R.st p = i ∧ R.slotJ p t = j ∧ R.slotK p t = k
  · obtain ⟨p, t, rfl, rfl, rfl⟩ := hex
    rw [hA.ce_slot p t r hr l hl, hA'.ce_slot p t r hr l hl]
  · rw [hA.ce_zero i hi j hj k hk r hr l hl fun p t h => hex ⟨p, t, h⟩,
      hA'.ce_zero i hi j hj k hk r hr l hl fun p t h => hex ⟨p, t, h⟩]

theorem shapes_eq (hA : R.Agrees μ T S C) (hA' : R.Agrees μ' T' S C') : μ = μ' := by
  funext e
  apply Subtype.ext
  apply youngDiagram_ext_rowLen
  intro r
  rcases lt_or_ge r P.n with hr | hr
  · have h := (hA.sh_arrow e r hr).symm.trans (hA'.sh_arrow e r hr)
    exact_mod_cast h
  · have h1 := (μ e).2
    have h2 := (μ' e).2
    have hd : min (Q.dim (Q.src e)) (Q.dim (Q.tgt e)) ≤ P.n :=
      (min_le_left _ _).trans (R.dim_le _)
    rw [YoungDiagram.rowLen_eq_zero_of_colLen_le (by omega),
      YoungDiagram.rowLen_eq_zero_of_colLen_le (by omega)]

theorem tabs_eq {T'' : Q.Tabs μ} (hA : R.Agrees μ T S C) (hA' : R.Agrees μ T'' S C) :
    T = T'' := by
  funext p t
  apply (rowCountsEquiv _ (ForwardQuiver.colLen_vertexFactors μ p t)).injective
  apply Subtype.ext
  funext r l
  have hdn := R.dim_le p
  have h := (hA.ce_slot p t r (by omega) l (by omega)).symm.trans
    (hA'.ce_slot p t r (by omega) l (by omega))
  show rowCount (T p t).1 r l = rowCount (T'' p t).1 r l
  exact_mod_cast h

end Agrees

/-! ### The bijection -/

/-- The point of arrow shapes and LR chains, as a point satisfying the conditions. -/
def encodeChains (a : Σ μ : Q.ArrowShapes, Q.VertexChains μ lam) :
    {x : Fin P.dim → ℤ // P.Conditions (P.sh x) (P.ce x)} :=
  ⟨R.encode a.1 fun p => (a.2 p).1,
    (R.agrees_encode a.1 _).conditions_iff.mpr fun p => (a.2 p).2⟩

theorem encodeChains_injective : Function.Injective R.encodeChains := by
  rintro ⟨μ, T⟩ ⟨μ', T'⟩ h
  have hx : R.encode μ (fun p => (T p).1) = R.encode μ' (fun p => (T' p).1) :=
    congrArg Subtype.val h
  have hA := R.agrees_encode μ fun p => (T p).1
  have hA' := R.agrees_encode μ' fun p => (T' p).1
  rw [← hx] at hA'
  obtain rfl := hA.shapes_eq hA'
  have hT := hA.tabs_eq hA'
  congr 1
  funext p
  exact Subtype.ext (congrFun hT p)

theorem encodeChains_surjective : Function.Surjective R.encodeChains := by
  rintro ⟨x, hx⟩
  have hA := R.agrees_of hx
  refine ⟨⟨R.shapesOf hx, fun p => ⟨R.tabsOf hx p, (hA.conditions_iff.mp hx) p⟩⟩,
    Subtype.ext ?_⟩
  have hE := R.agrees_encode (R.shapesOf hx) (R.tabsOf hx)
  apply P.eq_of_coords
  · intro i hi j hj k hk r hr
    exact hE.sh_eq hA hi hj hk hr
  · intro i hi j hj k hk r hr l hl
    exact hE.ce_eq hA hi hj hk hr hl

/-- **The points satisfying the conditions are the arrow shapes with LR chains.** -/
def conditionsEquiv :
    {x : Fin P.dim → ℤ // P.Conditions (P.sh x) (P.ce x)} ≃
      Σ μ : Q.ArrowShapes, Q.VertexChains μ lam :=
  (Equiv.ofBijective R.encodeChains ⟨R.encodeChains_injective, R.encodeChains_surjective⟩).symm

end

end Realizes

end PositionalQuiver

end Flat

end Schubert.RS.Quiver
