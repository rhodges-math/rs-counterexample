import RSCounterexample.Paper.LR.Main

/-!
# Littlewood–Richardson chains

A vertex factor is a determinant twist of a Schur polynomial, `det^σ · s_ν`
(`Schubert.RS.Quiver.Schur.VertexFactor`). For a sequence `F_0, …, F_{m−1}` of them, an
**LR chain** ending at `λ` is a sequence of semistandard tableaux `T_t` of the shapes `ν_t`, in the
letters `0, …, d − 1`, such that every `T_t` is lattice from the running weight
`κ_t = ∑_{t' < t} (σ_{t'} + wt T_{t'})`, and `κ_m = λ`. Iterating the Littlewood–Richardson rule,
the multiplicity of `s_λ` in `∏_t det^{σ_t} s_{ν_t}` is the number of LR chains ending at `λ`
(`Schubert.RS.Quiver.Schur.weylProjector_prod_character`).

A tableau of shape `ν` (at most `d` rows) is determined by its row counts `c r k` (the number of
`k`s in row `r`), subject to linear constraints (`Schubert.RS.Quiver.Schur.rowCountsEquiv`). In
these coordinates the lattice condition is also linear
(`Schubert.RS.Quiver.Schur.isLattice_iff_rowCounts`), so LR chains are the lattice points of a
polytope, as used in the counting algorithm of Theorem 1.4.

## Main definitions

* `Schubert.RS.Quiver.Schur.VertexFactor`, `VertexFactor.character`.
* `Schubert.RS.Quiver.Schur.runningWeight`, `IsLRChain`, `LRChain`.
* `Schubert.RS.Quiver.Schur.rowCounts`, `RowCountConstraints`, `rowCountsEquiv`.

## Main results

* `Schubert.RS.Quiver.Schur.alternant_mul_prod_character`: the iterated LR rule, alternant form.
* `Schubert.RS.Quiver.Schur.weylProjector_prod_character`: multiplicities count LR chains.
* `Schubert.RS.Quiver.Schur.rowCountsEquiv`, `isLattice_iff_rowCounts`,
  `weightVec_eq_sum_rowCounts`.
-/

namespace Schubert.RS.Quiver.Schur

noncomputable section

open Equiv Schubert.RS.LR SemistandardYoungTableau

/-! ## Vertex factors and chains -/

/-- A vertex factor `det^shift · s_shape`. -/
structure VertexFactor where
  /-- The shape of the Schur polynomial. -/
  shape : YoungDiagram
  /-- The power of the determinant. -/
  shift : ℤ

/-- The character `det^σ s_ν` of a vertex factor, in `d` variables. -/
def VertexFactor.character (d : ℕ) (F : VertexFactor) : Laurent d :=
  shiftedSchur d F.shape F.shift

theorem isSymmetric_character (d : ℕ) (F : VertexFactor) : IsSymmetric (F.character d) :=
  isSymmetric_shiftedSchur F.shape F.shift

variable {d m : ℕ}

/-- The running weight before the factor `t`: `∑_{t' < t} (σ_{t'} + wt T_{t'})`. -/
def runningWeight (F : Fin m → VertexFactor)
    (T : (t : Fin m) → TauCeti.BoundedSSYT d (F t).shape) (t : ℕ) : Weight d :=
  ∑ t' : Fin m, if t'.val < t then (fun _ => (F t').shift) + weightVec (T t') else 0

/-- `T` is an **LR chain** ending at `λ`: every `T_t` is lattice from the running weight before
it, and the final running weight is `λ`. -/
def IsLRChain (F : Fin m → VertexFactor) (lam : Weight d)
    (T : (t : Fin m) → TauCeti.BoundedSSYT d (F t).shape) : Prop :=
  (∀ t : Fin m, IsLattice (runningWeight F T t) (T t).1) ∧ runningWeight F T m = lam

instance (F : Fin m → VertexFactor) (lam : Weight d) : DecidablePred (IsLRChain F lam) :=
  fun _ => by unfold IsLRChain; infer_instance

/-- **The LR chains** of a sequence of vertex factors ending at `λ`. -/
abbrev LRChain (F : Fin m → VertexFactor) (lam : Weight d) : Type :=
  {T : (t : Fin m) → TauCeti.BoundedSSYT d (F t).shape // IsLRChain F lam T}

@[simp]
theorem runningWeight_zero (F : Fin m → VertexFactor)
    (T : (t : Fin m) → TauCeti.BoundedSSYT d (F t).shape) : runningWeight F T 0 = 0 := by
  simp [runningWeight]

theorem runningWeight_cons_succ (F : Fin (m + 1) → VertexFactor)
    (S : TauCeti.BoundedSSYT d (F 0).shape)
    (T : (t : Fin m) → TauCeti.BoundedSSYT d (F t.succ).shape) (t : ℕ) :
    runningWeight F (Fin.cons (α := fun t => TauCeti.BoundedSSYT d (F t).shape) S T) (t + 1) =
      ((fun _ => (F 0).shift) + weightVec S) + runningWeight (fun i => F i.succ) T t := by
  rw [runningWeight, Fin.sum_univ_succ, runningWeight]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ]
  rw [ite_eq_left (Nat.succ_pos t)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Nat.add_lt_add_iff_right]

theorem isLattice_cons_succ_iff (F : Fin (m + 1) → VertexFactor) (κ : Weight d)
    (S : TauCeti.BoundedSSYT d (F 0).shape)
    (T : (t : Fin m) → TauCeti.BoundedSSYT d (F t.succ).shape) :
    (∀ t : Fin (m + 1), IsLattice (κ + runningWeight F
        (Fin.cons (α := fun t => TauCeti.BoundedSSYT d (F t).shape) S T) t)
        ((Fin.cons (α := fun t => TauCeti.BoundedSSYT d (F t).shape) S T) t).1) ↔
      IsLattice κ S.1 ∧ ∀ t : Fin m, IsLattice ((κ + ((fun _ => (F 0).shift) + weightVec S)) +
        runningWeight (fun i => F i.succ) T t) (T t).1 := by
  rw [Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, runningWeight_zero, add_zero,
    Fin.val_succ, runningWeight_cons_succ, add_assoc]

theorem sum_pi_fin_succ {M : Type*} [AddCommMonoid M] {α : Fin (m + 1) → Type*}
    [∀ t, Fintype (α t)] (f : ((t : Fin (m + 1)) → α t) → M) :
    ∑ T, f T = ∑ S : α 0, ∑ T : (t : Fin m) → α t.succ, f (Fin.cons S T) := by
  rw [← (Fin.consEquiv α).sum_comp, Fintype.sum_prod_type]
  rfl

/-- **The iterated Littlewood–Richardson rule**: for a weakly decreasing integer weight `κ`,
`a_{κ+δ} · ∏_t det^{σ_t} s_{ν_t} = ∑_T a_{κ + κ_m + δ}` over the sequences of tableaux each lattice
from `κ` plus the running weight before it. -/
theorem alternant_mul_prod_character (F : Fin m → VertexFactor) (κ : Weight d)
    (hκ : Antitone κ) :
    alternant (κ + staircase d) * ∏ t, (F t).character d =
      ∑ T : (t : Fin m) → TauCeti.BoundedSSYT d (F t).shape,
        if ∀ t : Fin m, IsLattice (κ + runningWeight F T t) (T t).1 then
          alternant (κ + runningWeight F T m + staircase d) else 0 := by
  induction m generalizing κ with
  | zero =>
    rw [Fin.prod_univ_zero, mul_one, Fintype.sum_unique]
    simp
  | succ m ih =>
    rw [Fin.prod_univ_succ, ← mul_assoc, VertexFactor.character,
      LR.alternant_mul_shiftedSchur κ hκ, Finset.sum_mul, Finset.sum_filter, sum_pi_fin_succ]
    refine Finset.sum_congr rfl fun S _ => ?_
    by_cases hS' : IsLattice κ S.1
    · rw [ite_eq_left hS']
      have hκ' : Antitone (κ + ((fun _ => (F 0).shift) + weightVec S)) := by
        have h1 := antitone_add_weightVec hS'
        have h2 : κ + ((fun _ => (F 0).shift) + weightVec S) =
            (κ + weightVec S) + fun _ => (F 0).shift := by abel
        rw [h2]
        exact h1.add antitone_const
      have h := ih (fun i => F i.succ) _ hκ'
      have e1 : κ + weightVec S + (fun _ => (F 0).shift) + staircase d =
          κ + ((fun _ => (F 0).shift) + weightVec S) + staircase d := by abel
      rw [e1, h]
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [runningWeight_cons_succ]
      simp only [isLattice_cons_succ_iff, hS', true_and, add_assoc]
    · rw [ite_eq_right hS']
      symm
      refine Finset.sum_eq_zero fun T _ => ?_
      exact ite_eq_right fun h => hS' ((isLattice_cons_succ_iff F κ S T).mp h).1

/-- Along a sequence of tableaux each lattice from the running weight, the running weights stay
weakly decreasing. -/
theorem antitone_runningWeight (F : Fin m → VertexFactor) (κ : Weight d) (hκ : Antitone κ)
    (T : (t : Fin m) → TauCeti.BoundedSSYT d (F t).shape)
    (hT : ∀ t : Fin m, IsLattice (κ + runningWeight F T t) (T t).1) :
    Antitone (κ + runningWeight F T m) := by
  induction m generalizing κ with
  | zero => simpa using hκ
  | succ m ih =>
    have hT' := hT
    rw [← Fin.cons_self_tail (α := fun t => TauCeti.BoundedSSYT d (F t).shape) T] at hT' ⊢
    rw [isLattice_cons_succ_iff] at hT'
    rw [runningWeight_cons_succ, ← add_assoc]
    have hκ' : Antitone (κ + ((fun _ => (F 0).shift) + weightVec (T 0))) := by
      have h1 := antitone_add_weightVec hT'.1
      have h2 : κ + ((fun _ => (F 0).shift) + weightVec (T 0)) =
          (κ + weightVec (T 0)) + fun _ => (F 0).shift := by abel
      rw [h2]
      exact h1.add antitone_const
    exact ih (fun i => F i.succ) _ hκ' (Fin.tail T) hT'.2

theorem isSymmetric_prod_character (F : Fin m → VertexFactor) :
    IsSymmetric (∏ t, (F t).character d) := fun σ => by
  rw [map_prod]
  exact Finset.prod_congr rfl fun t _ => isSymmetric_character d (F t) σ

/-- **Multiplicities in products of vertex factors count LR chains**: for a dominant weight `λ`,
the coefficient of `s_λ` in `∏_t det^{σ_t} s_{ν_t}` is the number of LR chains ending at `λ`. -/
theorem weylProjector_prod_character (F : Fin m → VertexFactor) (lam : TauCeti.DominantWeight d) :
    weylProjector (lam.1 ∘ ⇑(Fin.revPerm : Perm (Fin d))) (∏ t, (F t).character d) =
      Fintype.card (LRChain F lam.1) := by
  classical
  rw [weylProjector_eq_alternant (isSymmetric_prod_character F), LR.revPerm_comp_twice]
  have h := alternant_mul_prod_character F (0 : Weight d) antitone_const
  simp only [zero_add] at h
  rw [h, AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  have hterm : ∀ T : (t : Fin m) → TauCeti.BoundedSSYT d (F t).shape,
      (if ∀ t : Fin m, IsLattice (runningWeight F T t) (T t).1 then
        alternant (runningWeight F T m + staircase d) else 0).coeff (lam.1 + staircase d) =
        if IsLRChain F lam.1 T then 1 else 0 := by
    intro T
    by_cases hT : ∀ t : Fin m, IsLattice (runningWeight F T t) (T t).1
    · have hanti : Antitone (runningWeight F T m) := by
        simpa using antitone_runningWeight F 0 antitone_const T (by simpa using hT)
      rw [ite_eq_left hT, coeff_alternant_of_strictAnti (strictAnti_add_staircase hanti)
        (strictAnti_add_staircase lam.2)]
      by_cases he : runningWeight F T m = lam.1
      · simp [IsLRChain, hT, he]
      · have he' : runningWeight F T m + staircase d ≠ lam.1 + staircase d :=
          fun e => he (add_right_cancel e)
        simp [IsLRChain, he, he']
    · rw [ite_eq_right hT]
      simp [IsLRChain, hT]
  simp only [hterm]
  rw [Finset.sum_boole, Fintype.card_subtype]

/-- The number of LR chains does not depend on the order of the factors. -/
theorem card_LRChain_comp (F : Fin m → VertexFactor) (e : Fin m ≃ Fin m)
    (lam : TauCeti.DominantWeight d) :
    Fintype.card (LRChain (F ∘ e) lam.1) = Fintype.card (LRChain F lam.1) := by
  have h1 := weylProjector_prod_character (F ∘ e) lam
  have h2 := weylProjector_prod_character F lam
  rw [show ∏ t, (Function.comp F e t).character d = ∏ t, (F t).character d from
    Equiv.prod_comp e fun t => (F t).character d] at h1
  exact_mod_cast h1.symm.trans h2

/-! ## Row counts -/

section RowCounts

variable {ν : YoungDiagram}

/-! ### Sums over `Fin d` as sums over ranges -/

theorem sum_fin_eq_sum_range {M : Type*} [AddCommMonoid M] (g : Fin d → M) (f : ℕ → M)
    (hgf : ∀ k : Fin d, g k = f k) : ∑ k, g k = ∑ k ∈ Finset.range d, f k := by
  rw [Finset.sum_congr rfl fun k _ => hgf k, Fin.sum_univ_eq_sum_range f d]

theorem sum_fin_filter_le {M : Type*} [AddCommMonoid M] (g : Fin d → M) (f : ℕ → M)
    (hgf : ∀ k : Fin d, g k = f k) (k : Fin d) :
    ∑ k' ∈ Finset.univ.filter (· ≤ k), g k' = ∑ k' ∈ Finset.range (k + 1), f k' := by
  rw [Finset.sum_congr rfl fun k' _ => hgf k',
    ← Finset.sum_image (f := f) (g := Fin.val) fun x _ y _ h => Fin.ext h]
  congr 1
  ext y
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Nat.lt_succ_of_le hx
  · intro hy
    exact ⟨⟨y, by have := k.isLt; omega⟩, Nat.le_of_lt_succ hy, rfl⟩

theorem sum_fin_filter_lt {M : Type*} [AddCommMonoid M] (g : Fin d → M) (f : ℕ → M)
    (hgf : ∀ k : Fin d, g k = f k) (k : Fin d) :
    ∑ k' ∈ Finset.univ.filter (· < k), g k' = ∑ k' ∈ Finset.range k, f k' := by
  rw [Finset.sum_congr rfl fun k' _ => hgf k',
    ← Finset.sum_image (f := f) (g := Fin.val) fun x _ y _ h => Fin.ext h]
  congr 1
  ext y
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    exact ⟨⟨y, by have := k.isLt; omega⟩, hy, rfl⟩

/-! ### Row counts -/

theorem rowCountLt_zero (T : _root_.SemistandardYoungTableau ν) (r : ℕ) :
    rowCountLt T r 0 = 0 := by
  simp [rowCountLt]

theorem sum_range_rowCount (T : _root_.SemistandardYoungTableau ν) (r K : ℕ) :
    ∑ k ∈ Finset.range K, rowCount T r k = rowCountLt T r K := by
  induction K with
  | zero => simp [rowCountLt_zero]
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, rowCount]
    have := T.rowCountLt_mono r (by omega : K ≤ K + 1)
    omega

/-- The row counts of a tableau in the letters `0, …, d − 1`: `c r k` is the number of `k`s in
row `r`. -/
def rowCounts (T : TauCeti.BoundedSSYT d ν) (r k : Fin d) : ℕ := rowCount T.1 r k

/-- **The row-count constraints**: row `r` has `ν_r` cells, and row `r + 1` has at most as many
entries `≤ k` as row `r` has entries `< k` (the columns increase strictly). -/
def RowCountConstraints (ν : YoungDiagram) (c : Fin d → Fin d → ℕ) : Prop :=
  (∀ r : Fin d, ∑ k, c r k = ν.rowLen r) ∧
    ∀ (r : ℕ) (hr : r + 1 < d) (k : Fin d),
      ∑ k' ∈ Finset.univ.filter (· ≤ k), c ⟨r + 1, hr⟩ k' ≤
        ∑ k' ∈ Finset.univ.filter (· < k), c ⟨r, by omega⟩ k'

theorem rowCountLt_eq_rowLen (T : TauCeti.BoundedSSYT d ν) (r : ℕ) :
    rowCountLt T.1 r d = ν.rowLen r := by
  have h := T.1.rowCountLt_le_rowLen r d
  have h2 : ν.rowLen r ≤ rowCountLt T.1 r d := by
    rw [rowCountLt]
    rw [Finset.filter_true_of_mem fun j hj => T.2 r j
      (YoungDiagram.mem_iff_lt_rowLen.mpr (Finset.mem_range.mp hj))]
    simp
  omega

/-- The row counts of a tableau satisfy the row-count constraints. -/
theorem rowCountConstraints_rowCounts (T : TauCeti.BoundedSSYT d ν) :
    RowCountConstraints ν (rowCounts T) := by
  refine ⟨fun r => ?_, fun r hr k => ?_⟩
  · rw [sum_fin_eq_sum_range (rowCounts T r) (fun k => rowCount T.1 r k) fun _ => rfl,
      sum_range_rowCount, rowCountLt_eq_rowLen]
  · rw [sum_fin_filter_le (rowCounts T ⟨r + 1, hr⟩) (fun k' => rowCount T.1 (r + 1) k')
      (fun _ => rfl), sum_fin_filter_lt (rowCounts T ⟨r, by omega⟩) (fun k' => rowCount T.1 r k')
      (fun _ => rfl), sum_range_rowCount, sum_range_rowCount]
    exact T.1.rowCountLt_succ_le r k

/-! ### The tableau of a row-count matrix -/

variable (c : Fin d → Fin d → ℕ)

/-- The row counts, extended by zero to all of `ℕ × ℕ`. -/
def cNat (r k : ℕ) : ℕ := if h : r < d ∧ k < d then c ⟨r, h.1⟩ ⟨k, h.2⟩ else 0

/-- The number of entries `≤ k` in row `r`. -/
def cum (r k : ℕ) : ℕ := ∑ k' ∈ Finset.range (k + 1), cNat c r k'

/-- The entry of the tableau of a row-count matrix: the number of letters `k < d` whose
cumulative count is at most the column. -/
def entryOf (ν : YoungDiagram) (r j : ℕ) : ℕ :=
  if (r, j) ∈ ν then ((Finset.range d).filter fun k => cum c r k ≤ j).card else 0

variable {c}

theorem cNat_fin {r : ℕ} (hr : r < d) (k : Fin d) : cNat c r k = c ⟨r, hr⟩ k := by
  simp [cNat, hr, k.isLt]

theorem cum_mono (r : ℕ) {k k' : ℕ} (h : k ≤ k') : cum c r k ≤ cum c r k' :=
  Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))

theorem cum_last (hc : RowCountConstraints ν c) {r : ℕ} (hr : r < d) :
    cum c r (d - 1) = ν.rowLen r := by
  have h := hc.1 ⟨r, hr⟩
  rw [sum_fin_eq_sum_range _ (fun k => cNat c r k) fun k => (cNat_fin hr k).symm] at h
  rw [cum, Nat.sub_add_cancel (by omega)]
  exact h

theorem cum_succ_le (hc : RowCountConstraints ν c) {r : ℕ} (hr : r + 1 < d) {k : ℕ}
    (hk : k + 1 < d) : cum c (r + 1) (k + 1) ≤ cum c r k := by
  have h := hc.2 r hr ⟨k + 1, hk⟩
  rw [sum_fin_filter_le _ (fun k' => cNat c (r + 1) k') (fun k' => (cNat_fin hr k').symm),
    sum_fin_filter_lt _ (fun k' => cNat c r k') (fun k' => (cNat_fin (by omega) k').symm)] at h
  exact h

theorem cum_succ_zero (hc : RowCountConstraints ν c) {r : ℕ} (hr : r + 1 < d) :
    cum c (r + 1) 0 = 0 := by
  have h := hc.2 r hr ⟨0, by omega⟩
  rw [sum_fin_filter_le _ (fun k' => cNat c (r + 1) k') (fun k' => (cNat_fin hr k').symm),
    sum_fin_filter_lt _ (fun k' => cNat c r k') (fun k' => (cNat_fin (by omega) k').symm)] at h
  simpa [cum] using h

/-- The letters whose cumulative count is at most `j` form an initial segment. -/
theorem entryOf_lt_iff {r j : ℕ} (hrj : (r, j) ∈ ν) {x : ℕ} (hx : 1 ≤ x) (hxd : x ≤ d) :
    entryOf c ν r j < x ↔ j < cum c r (x - 1) := by
  rw [entryOf, ite_eq_left hrj]
  constructor
  · intro h
    by_contra hle
    have hsub : Finset.range x ⊆ (Finset.range d).filter fun k => cum c r k ≤ j := by
      intro k hk
      rw [Finset.mem_range] at hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
        (cum_mono r (by omega)).trans (not_lt.mp hle)⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    omega
  · intro h
    have hsub : ((Finset.range d).filter fun k => cum c r k ≤ j) ⊆ Finset.range (x - 1) := by
      intro k hk
      rw [Finset.mem_filter] at hk
      rw [Finset.mem_range]
      by_contra hk'
      have := cum_mono (c := c) r (not_lt.mp hk')
      omega
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    omega

theorem lt_of_mem_of_colLen_le {r j : ℕ} (hrj : (r, j) ∈ ν) (hν : ν.colLen 0 ≤ d) : r < d :=
  lt_of_lt_of_le (YoungDiagram.mem_iff_lt_colLen.mp (ν.up_left_mem le_rfl (Nat.zero_le j) hrj)) hν

theorem entryOf_lt (hc : RowCountConstraints ν c) {r j : ℕ} (hrj : (r, j) ∈ ν)
    (hν : ν.colLen 0 ≤ d) : entryOf c ν r j < d := by
  have hr := lt_of_mem_of_colLen_le hrj hν
  rw [entryOf_lt_iff hrj (by omega) le_rfl, cum_last hc hr]
  exact YoungDiagram.mem_iff_lt_rowLen.mp hrj

theorem entryOf_col_strict_succ (hc : RowCountConstraints ν c) (hν : ν.colLen 0 ≤ d) {r j : ℕ}
    (hrj : (r + 1, j) ∈ ν) : entryOf c ν r j < entryOf c ν (r + 1) j := by
  have hrj' : (r, j) ∈ ν := ν.up_left_mem (Nat.le_succ r) le_rfl hrj
  have hr1 : r + 1 < d := lt_of_mem_of_colLen_le hrj hν
  have hlen : j < ν.rowLen r := YoungDiagram.mem_iff_lt_rowLen.mp hrj'
  rw [entryOf, ite_eq_left hrj', entryOf, ite_eq_left hrj]
  set A := (Finset.range d).filter fun k => cum c r k ≤ j
  set B := (Finset.range d).filter fun k => cum c (r + 1) k ≤ j
  have hA : ∀ k ∈ A, k + 1 < d := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    by_contra hk'
    have hk1 : k = d - 1 := by omega
    have := cum_last hc (r := r) (by omega)
    rw [← hk1] at this
    omega
  have hsub : insert 0 (A.image (· + 1)) ⊆ B := by
    intro k hk
    rw [Finset.mem_insert, Finset.mem_image] at hk
    rcases hk with rfl | ⟨k', hk', rfl⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
        by rw [cum_succ_zero hc hr1]; omega⟩
    · have h1 := hA k' hk'
      rw [Finset.mem_filter] at hk'
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h1,
        (cum_succ_le hc hr1 h1).trans hk'.2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp), Finset.card_image_of_injective _
    (add_left_injective 1)] at hcard
  omega

/-- **The tableau of a row-count matrix.** -/
def ofRowCounts (ν : YoungDiagram) (hν : ν.colLen 0 ≤ d) (hc : RowCountConstraints ν c) :
    TauCeti.BoundedSSYT d ν :=
  ⟨{ entry := entryOf c ν
     row_weak' := fun {r j₁ j₂} hj hrj => by
       have hrj₁ : (r, j₁) ∈ ν := ν.up_left_mem le_rfl hj.le hrj
       rw [entryOf, ite_eq_left hrj₁, entryOf, ite_eq_left hrj]
       exact Finset.card_le_card fun k hk => by
         rw [Finset.mem_filter] at hk ⊢
         exact ⟨hk.1, hk.2.trans hj.le⟩
     col_strict' := fun {r₁ r₂ j} hr hrj => by
       obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hr
       clear hr
       induction m with
       | zero => exact entryOf_col_strict_succ hc hν hrj
       | succ m ih =>
         have hrj' : (r₁ + m + 1, j) ∈ ν := ν.up_left_mem (by omega) le_rfl hrj
         exact (ih hrj').trans (entryOf_col_strict_succ hc hν (by
           rwa [show r₁ + (m + 1) + 1 = r₁ + m + 1 + 1 by omega] at hrj))
     zeros' := fun {r j} hrj => by rw [entryOf, ite_eq_right hrj] },
    fun r j hrj => entryOf_lt hc hrj hν⟩

theorem rowCountLt_ofRowCounts (hν : ν.colLen 0 ≤ d) (hc : RowCountConstraints ν c) {r : ℕ}
    (hr : r < d) {x : ℕ} (hx : 1 ≤ x) (hxd : x ≤ d) :
    rowCountLt (ofRowCounts ν hν hc).1 r x = cum c r (x - 1) := by
  have hle : cum c r (x - 1) ≤ ν.rowLen r := by
    rw [← cum_last hc hr]
    exact cum_mono r (by omega)
  rw [rowCountLt]
  have hfilter : ((Finset.range (ν.rowLen r)).filter
      fun j => (ofRowCounts ν hν hc).1 r j < x) = Finset.range (cum c r (x - 1)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hj, hlt⟩
      exact (entryOf_lt_iff (YoungDiagram.mem_iff_lt_rowLen.mpr hj) hx hxd).mp hlt
    · intro hj
      have hj' : j < ν.rowLen r := lt_of_lt_of_le hj hle
      exact ⟨hj', (entryOf_lt_iff (YoungDiagram.mem_iff_lt_rowLen.mpr hj') hx hxd).mpr hj⟩
  rw [hfilter, Finset.card_range]

theorem rowCounts_ofRowCounts (hν : ν.colLen 0 ≤ d) (hc : RowCountConstraints ν c) :
    rowCounts (ofRowCounts ν hν hc) = c := by
  funext r k
  have hk1 := k.isLt
  rw [rowCounts, rowCount, rowCountLt_ofRowCounts hν hc r.isLt (by omega) (by omega)]
  rcases Nat.eq_zero_or_pos (k : ℕ) with hk | hk
  · rw [hk, rowCountLt_zero]
    have : cNat c r 0 = c r k := by
      rw [show (0 : ℕ) = (k : ℕ) by omega, cNat_fin r.isLt k]
    simp [cum, this]
  · rw [rowCountLt_ofRowCounts hν hc r.isLt (by omega) (by omega)]
    have e1 : (k : ℕ) + 1 - 1 = (k - 1) + 1 := by omega
    rw [e1, cum, Finset.sum_range_succ, ← cum, Nat.sub_add_cancel hk, cNat_fin r.isLt k]
    simp

theorem ofRowCounts_rowCounts (hν : ν.colLen 0 ≤ d) (T : TauCeti.BoundedSSYT d ν) :
    ofRowCounts ν hν (rowCountConstraints_rowCounts T) = T := by
  have hcum : ∀ r k : ℕ, r < d → k < d → cum (rowCounts T) r k = rowCountLt T.1 r (k + 1) := by
    intro r k hr hk
    rw [cum, ← sum_range_rowCount]
    refine Finset.sum_congr rfl fun k' hk' => ?_
    rw [Finset.mem_range] at hk'
    simp [cNat, rowCounts, hr, show k' < d by omega]
  apply Subtype.ext
  ext r j
  change entryOf (rowCounts T) ν r j = T.1 r j
  by_cases hrj : (r, j) ∈ ν
  · have hr := lt_of_mem_of_colLen_le hrj hν
    have hjlen := YoungDiagram.mem_iff_lt_rowLen.mp hrj
    have hTd := T.2 r j hrj
    rw [entryOf, ite_eq_left hrj]
    have hset : ((Finset.range d).filter fun k => cum (rowCounts T) r k ≤ j) =
        Finset.range (T.1 r j) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hk, hle⟩
        rw [hcum r k hr hk] at hle
        by_contra hk'
        have := (T.1.lt_rowCountLt_iff (x := k + 1) hjlen).mpr (by omega)
        omega
      · intro hk
        refine ⟨by omega, ?_⟩
        rw [hcum r k hr (by omega)]
        by_contra hle
        have := (T.1.lt_rowCountLt_iff (x := k + 1) hjlen).mp (not_le.mp hle)
        omega
    rw [hset, Finset.card_range]
  · rw [entryOf, ite_eq_right hrj, T.1.zeros hrj]

/-- **Tableaux are their row counts**: for a shape with at most `d` rows, a tableau in the letters
`0, …, d − 1` is the same thing as a matrix of row counts satisfying the row-count
constraints. -/
def rowCountsEquiv (ν : YoungDiagram) (hν : ν.colLen 0 ≤ d) :
    TauCeti.BoundedSSYT d ν ≃ {c : Fin d → Fin d → ℕ // RowCountConstraints ν c} where
  toFun T := ⟨rowCounts T, rowCountConstraints_rowCounts T⟩
  invFun c := ofRowCounts ν hν c.2
  left_inv T := ofRowCounts_rowCounts hν T
  right_inv c := Subtype.ext (rowCounts_ofRowCounts hν c.2)

theorem rowCountsEquiv_apply (hν : ν.colLen 0 ≤ d) (T : TauCeti.BoundedSSYT d ν) :
    (rowCountsEquiv ν hν T : Fin d → Fin d → ℕ) = rowCounts T :=
  rfl

/-- **The weight of a tableau from its row counts.** -/
theorem weightVec_eq_sum_rowCounts (hν : ν.colLen 0 ≤ d) (T : TauCeti.BoundedSSYT d ν)
    (i : Fin d) : weightVec T i = ∑ r, (rowCounts T r i : ℤ) := by
  rw [weightVec, content_eq_countBelow_of_le T.1 i hν, countBelow, Nat.cast_sum,
    sum_fin_eq_sum_range (fun r => (rowCounts T r i : ℤ)) (fun r => (rowCount T.1 r i : ℤ))
      fun _ => rfl]

/-- **The lattice condition in row counts**: for every row `r < d` and letter `i` with
`i + 1 < d`, `κ_{i+1} + ∑_{r' ≤ r} c r' (i + 1) ≤ κ_i + ∑_{r' < r} c r' i`. -/
theorem isLattice_iff_rowCounts (hν : ν.colLen 0 ≤ d) (κ : Weight d)
    (T : TauCeti.BoundedSSYT d ν) :
    IsLattice κ T.1 ↔ ∀ (r : Fin d) (i : ℕ) (hi : i + 1 < d),
      κ ⟨i + 1, hi⟩ + ∑ r' ∈ Finset.univ.filter (· ≤ r), (rowCounts T r' ⟨i + 1, hi⟩ : ℤ) ≤
        κ ⟨i, by omega⟩ +
          ∑ r' ∈ Finset.univ.filter (· < r), (rowCounts T r' ⟨i, by omega⟩ : ℤ) := by
  have hle : ∀ (r : Fin d) (x : Fin d), ∑ r' ∈ Finset.univ.filter (· ≤ r),
      (rowCounts T r' x : ℤ) = (countBelow T.1 (r + 1) x : ℤ) := by
    intro r x
    rw [sum_fin_filter_le (fun r' => (rowCounts T r' x : ℤ)) (fun r' => (rowCount T.1 r' x : ℤ))
      (fun _ => rfl), countBelow, Nat.cast_sum]
  have hlt : ∀ (r : Fin d) (x : Fin d), ∑ r' ∈ Finset.univ.filter (· < r),
      (rowCounts T r' x : ℤ) = (countBelow T.1 r x : ℤ) := by
    intro r x
    rw [sum_fin_filter_lt (fun r' => (rowCounts T r' x : ℤ)) (fun r' => (rowCount T.1 r' x : ℤ))
      (fun _ => rfl), countBelow, Nat.cast_sum]
  constructor
  · intro h r i hi
    have h1 := h r i hi
    rw [kap_of_lt κ hi, kap_of_lt κ (by omega)] at h1
    rw [hle, hlt]
    exact h1
  · intro h r i hi
    rw [kap_of_lt κ hi, kap_of_lt κ (by omega)]
    rcases lt_or_ge r d with hr | hr
    · have h1 := h ⟨r, hr⟩ i hi
      rw [hle, hlt] at h1
      exact h1
    · have h1 := h ⟨d - 1, by omega⟩ i hi
      rw [hle, hlt] at h1
      simp only at h1
      have e1 : d - 1 + 1 = d := by omega
      rw [e1] at h1
      have hc1 : countBelow T.1 (r + 1) (i + 1) = countBelow T.1 d (i + 1) := by
        rw [countBelow_of_colLen_le _ _ (by omega), countBelow_of_colLen_le _ _ hν]
      have hc2 : countBelow T.1 (d - 1) i ≤ countBelow T.1 r i :=
        countBelow_mono _ _ (by omega)
      rw [hc1]
      have : (countBelow T.1 (d - 1) i : ℤ) ≤ countBelow T.1 r i := by exact_mod_cast hc2
      linarith

end RowCounts

end

end Schubert.RS.Quiver.Schur
