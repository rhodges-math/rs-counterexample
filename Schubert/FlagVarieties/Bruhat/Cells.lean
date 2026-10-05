import Schubert.FlagVarieties.Normality.Fulton.KazhdanLusztigPatch
import Schubert.FlagVarieties.Normality.Fulton.Descent
import Schubert.FlagVarieties.PointModel.ClosureRelation
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field

/-!
# Bruhat cells

Over a field `K`, in the ring model (`FlagVarieties.PointModel`): `bruhatCell K w = B ẇ B`
is the preimage in `GL_n(K)` of the Bruhat cell `C_w = B ẇ B / B ⊆ Fl_n`.

* `eq_of_mem_bruhatCell`: **the Bruhat cells are disjoint** (prefix minors).
* `forall_cellIdeal_iff`: **`π⁻¹ X_w(K) = ⊔_{v ≤ w} B v̇ B`**: the zero set of the ideal of
  `B ẇ B` is the union of the cells `B v̇ B`, `v ≤ w` (`K` infinite, with the standard-monomial
  inputs). Consequently `cellIdeal_le_cellIdeal_iff`: `X_v ⊆ X_w ⟺ v ≤ w`.
* `CellVar w`: the coordinates `(r, c)` of the chart `v̇ U⁻` at `v = w` with `r < w c`;
  `card_cellVar`: there are `ℓ(w)` of them.
* `mem_bruhatCell_kazhdanLusztigPoint_iff`: a point of the chart `ẇ U⁻` lies in `B ẇ B` iff its
  coordinates below the pivots vanish. Hence (`exists_cellPoint_mul`, `cellPoint_mem_bruhatCell`,
  `eq_of_cellPoint_mul`) **`y ↦ cellPoint w y B` is a bijection `K^{ℓ(w)} ≃ C_w(K)`**.
* `kazhdanLusztigPatch_self`: the Kazhdan–Lusztig patch of `X_w` at `w` is the cell `C_w`;
  scheme-theoretically (`map_kazhdanLusztigSubst_fultonIdeal_self`, `K` algebraically closed of
  characteristic `0`) it is the coordinate subspace of the chart cut out by the coordinates below
  the pivots, and `ringKrullDim_kazhdanLusztigPatch_self`: its coordinate ring is a polynomial ring
  in `ℓ(w)` variables, of Krull dimension `ℓ(w)`: **`C_w ≅ 𝔸^{ℓ(w)}`**.
-/

open Schubert Demazure.FlagModule Demazure.SchubertUnions FinPermutation
open GLRep (glEval)

namespace FlagVarieties.PointModel

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {n : ℕ}

instance (v : Equiv.Perm (Fin n)) : Fintype (ChartVar v) := by
  unfold ChartVar
  infer_instance

instance (v : Equiv.Perm (Fin n)) : DecidableEq (ChartVar v) := by
  unfold ChartVar
  infer_instance

/-! ### Disjointness and closure -/

theorem mem_orbitSet_grassSet_of_mem_bruhatCell {v : Equiv.Perm (Fin n)} {g : GL (Fin n) K}
    (hg : g ∈ bruhatCell K v) (k : Fin n) : g ∈ orbitSet K (grassSet k (flagPrefixRows v k)) :=
  mem_orbitSet.mpr ⟨v, mem_grassSet.mpr (galeLE_refl _), hg⟩

/-- On `B v̇ B`, the chart minors of `w` are all nonzero only if `w ≤ v`. -/
theorem le_of_mem_bruhatCell_of_chartMinor_ne_zero {v w : Equiv.Perm (Fin n)} {g : GL (Fin n) K}
    (hg : g ∈ bruhatCell K v)
    (hw : ∀ c, evalAt (g : Matrix (Fin n) (Fin n) K) (chartMinor K w c) ≠ 0) : w ≤ᴮ v := by
  refine strongBruhat_iff_galeLE.mpr fun k => ?_
  by_contra hk
  apply hw k
  rw [evalAt_chartMinor_eq,
    evalAt_rowMinor_eq_zero_of_mem_orbitSet hk (mem_orbitSet_grassSet_of_mem_bruhatCell hg k),
    mul_zero]

/-- **The Bruhat cells are disjoint.** -/
theorem eq_of_mem_bruhatCell {v w : Equiv.Perm (Fin n)} {g : GL (Fin n) K}
    (hv : g ∈ bruhatCell K v) (hw : g ∈ bruhatCell K w) : v = w :=
  strongBruhat_antisymm
    (le_of_mem_bruhatCell_of_chartMinor_ne_zero hw (evalAt_chartMinor_ne_zero_of_mem_bruhatCell hv))
    (le_of_mem_bruhatCell_of_chartMinor_ne_zero hv (evalAt_chartMinor_ne_zero_of_mem_bruhatCell hw))

/-- **`π⁻¹ X_w(K) = ⋃_{v ≤ w} B v̇ B`**: the zero set in `GL_n(K)` of the ideal of `B ẇ B`. -/
theorem forall_cellIdeal_iff [Infinite K] (hSMT : StandardMonomialTheory K) (w : Equiv.Perm (Fin n))
    (g : GL (Fin n) K) :
    (∀ t ∈ cellIdeal K w, glEval g t = 0) ↔ ∃ v, v ≤ᴮ w ∧ g ∈ bruhatCell K v := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := exists_mem_bruhatCell g
    refine ⟨v, strongBruhat_iff_galeLE.mpr fun k => ?_, hv⟩
    by_contra hk
    have hmem : algebraMap (MatrixEntryPolynomial K n) (GLCoord K n)
        (rowMinor K k (flagPrefixRows v k).rows) ∈
        cellIdeal K w := fun g' hg' => by
      rw [glEval_algebraMap_eq_evalAt]
      exact evalAt_rowMinor_eq_zero_of_mem_orbitSet hk
          (mem_orbitSet_grassSet_of_mem_bruhatCell hg' k)
    have h0 := h _ hmem
    rw [glEval_algebraMap_eq_evalAt] at h0
    have hne := evalAt_chartMinor_ne_zero_of_mem_bruhatCell hv k
    rw [evalAt_chartMinor_eq, h0, mul_zero] at hne
    exact hne rfl
  · rintro ⟨v, hvw, hv⟩ t ht
    exact cellIdeal_le_cellIdeal hSMT hvw ht g hv

theorem permGL_mem_bruhatCell (v : Equiv.Perm (Fin n)) : permGL K v ∈ bruhatCell K v :=
  ⟨1, 1, isBorel_one, isBorel_one, by simp⟩

/-- **`X_v ⊆ X_w ⟺ v ≤ w`**, in the ring model. -/
theorem cellIdeal_le_cellIdeal_iff [Infinite K] (hSMT : StandardMonomialTheory K)
    {v w : Equiv.Perm (Fin n)} :
    cellIdeal K w ≤ cellIdeal K v ↔ v ≤ᴮ w := by
  refine ⟨fun h => ?_, cellIdeal_le_cellIdeal hSMT⟩
  obtain ⟨u, huw, hu⟩ := (forall_cellIdeal_iff hSMT w (permGL K v)).mp
    fun t ht => h ht _ (permGL_mem_bruhatCell v)
  rwa [eq_of_mem_bruhatCell hu (permGL_mem_bruhatCell v)] at huw

theorem orbitIdeal_lowerSet_le_iff [Infinite K] (hSMT : StandardMonomialTheory K)
    {v w : Equiv.Perm (Fin n)} :
    orbitIdeal K (lowerSet w) ≤ orbitIdeal K (lowerSet v) ↔ v ≤ᴮ w := by
  rw [orbitIdeal_lowerSet hSMT, orbitIdeal_lowerSet hSMT, cellIdeal_le_cellIdeal_iff hSMT]

/-! ### The coordinates of a cell -/

/-- The coordinates of the Bruhat cell `C_w`: chart coordinates `(r, c)` (`r ∉ w{0..c}`) with
`r < w c`. -/
def CellVar (w : Equiv.Perm (Fin n)) : Type :=
  {x : ChartVar w // x.1.1 < w x.1.2}

instance (w : Equiv.Perm (Fin n)) : Fintype (CellVar w) := by
  unfold CellVar
  infer_instance

/-- **The cell has `ℓ(w)` coordinates**: `(r, c) ↦ (c, w⁻¹ r)` is a bijection onto the
inversions. -/
theorem card_cellVar (w : Equiv.Perm (Fin n)) :
    Fintype.card (CellVar w) = FinPermutation.length w := by
  classical
  rw [FinPermutation.length, ← Fintype.card_coe]
  refine Fintype.card_congr
    { toFun := fun y => ⟨(y.1.1.2, w.symm y.1.1.1), ?_⟩
      invFun := fun p => ⟨⟨(w p.1.2, p.1.1), ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have h1 := y.1.2
    have h2 := y.2
    rw [FinPermutation.mem_inversionSet_iff]
    refine ⟨?_, by rwa [Equiv.apply_symm_apply]⟩
    by_contra hle
    exact h1 (w.symm y.1.1.1) (not_lt.mp hle) (Equiv.apply_symm_apply w _)
  · have hp := (FinPermutation.mem_inversionSet_iff w p.1.1 p.1.2).mp p.2
    intro j hj hjw
    have := w.injective hjw
    subst this
    exact absurd hj (not_le.mpr hp.1)
  · have hp := (FinPermutation.mem_inversionSet_iff w p.1.1 p.1.2).mp p.2
    exact hp.2
  · intro y
    apply Subtype.ext
    apply Subtype.ext
    simp
  · intro p
    apply Subtype.ext
    simp

/-! ### Points of the chart lying in the cell -/

/-- **Chart points below the pivots**: if the coordinates below the pivots vanish, the chart point
lies in `B ẇ B`; it is `u ẇ` with `u` upper unitriangular. -/
theorem kazhdanLusztigPoint_mem_bruhatCell (w : Equiv.Perm (Fin n)) (z : ChartVar w → K)
    (hz : ∀ x : ChartVar w, w x.1.2 < x.1.1 → z x = 0) :
    ∃ g ∈ bruhatCell K w, (g : Matrix (Fin n) (Fin n) K) = kazhdanLusztigPoint w z := by
  have hu : IsUnitriangular (kazhdanLusztigPoint w z * permMat K w⁻¹) := by
    refine ⟨fun i j hji => ?_, fun j => ?_⟩
    · change j < i at hji
      rw [mul_permMat]
      set c := w⁻¹ j with hc
      have hjc : j = w c := by rw [hc]; simp
      unfold kazhdanLusztigPoint
      split_ifs with h h'
      · exact hz _ (by rw [← hjc]; exact hji)
      · exact absurd (h'.trans hjc.symm) (ne_of_gt hji)
      · rfl
    · rw [mul_permMat]
      have := kazhdanLusztigPoint_self w z (w⁻¹ j)
      rwa [show w (w⁻¹ j) = j by simp] at this
  refine ⟨unitOfDet _ (by rw [det_of_isUnitriangular hu]; exact isUnit_one) * permGL K w,
    unitriangular_mul_mem_bruhatCell w hu, ?_⟩
  rw [Units.val_mul, coe_unitOfDet, coe_permGL, Matrix.mul_assoc, ← permMat_mul, inv_mul_cancel,
    permMat_one, Matrix.mul_one]

/-- A flag minor with permuted rows. -/
theorem evalAt_rowMinor_eq_sign (k : Fin n) (s : Fin (k.val + 1) → Fin n) {S : FlagMinorRowSet k}
    {σ : Equiv.Perm (Fin (k.val + 1))} (hS : ∀ i, S.rows (σ i) = s i)
    (M : Matrix (Fin n) (Fin n) K) :
    evalAt M (rowMinor K k s) = (Equiv.Perm.sign σ : K) * evalAt M (rowMinor K k S.rows) := by
  rw [evalAt_rowMinor, evalAt_rowMinor]
  have h : M.submatrix s (prefixIndex k) =
      (M.submatrix S.rows (prefixIndex k)).submatrix σ id := by
    ext a b
    simp [hS]
  rw [h, Matrix.det_permute]

/-- The count `#{x ∈ S | q ≤ x}` through the rows of `S`, permuted. -/
theorem card_filter_eq_sum {k : Fin n} (S : FlagMinorRowSet k) (q : Fin n)
    (σ : Equiv.Perm (Fin (k.val + 1))) :
    (S.val.filter fun x => q ≤ x).card = ∑ i, if q ≤ S.rows (σ i) then 1 else 0 := by
  classical
  have hS : S.val.filter (fun x => q ≤ x) =
      (Finset.univ.filter fun i => q ≤ S.rows i).image S.rows := by
    conv_lhs => rw [← Finset.image_orderEmbOfFin_univ S.val
      (Finset.mem_powersetCard.mp S.property).2]
    rw [Finset.filter_image]
    rfl
  rw [hS, Finset.card_image_of_injective _ S.rows.injective, Finset.card_filter,
    ← Equiv.sum_comp σ]

/-- The coordinates of a point of `B ẇ B` in the chart `ẇ U⁻` vanish below the pivots. -/
theorem eq_zero_of_kazhdanLusztigPoint_mem_bruhatCell {w : Equiv.Perm (Fin n)} {z : ChartVar w → K}
    {g : GL (Fin n) K} (hg : g ∈ bruhatCell K w)
    (hgz : (g : Matrix (Fin n) (Fin n) K) = kazhdanLusztigPoint w z) (x : ChartVar w)
    (hx : w x.1.2 < x.1.1) : z x = 0 := by
  classical
  set r := x.1.1
  set c := x.1.2
  have hinj : Function.Injective (snocRows w c r) := by
    intro a b hab
    simp only [snocRows] at hab
    split_ifs at hab with ha hb hb
    · exact Fin.ext (by simpa using congrArg Fin.val (w.injective hab))
    · exact absurd hab (x.2 ⟨a.val, by have := c.isLt; omega⟩ (show a.val ≤ c.val by omega))
    · exact absurd hab.symm (x.2 ⟨b.val, by have := c.isLt; omega⟩ (show b.val ≤ c.val by omega))
    · exact Fin.ext (by omega)
  obtain ⟨S, σ, hS⟩ := exists_sorted_rows c (snocRows w c r) hinj
  -- `S = {w 0, …, w (c-1), r}` is not below `w{0..c}`
  have hT : ¬ galeLE S (flagPrefixRows w c) := by
    intro hle
    have h1 := hle r
    rw [card_filter_eq_sum S r σ, card_filter_eq_sum (flagPrefixRows w c) r
      (flagPrefixPermutation w c)] at h1
    simp only [hS, flagPrefixPermutation_spec] at h1
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at h1
    have hlast : snocRows w c r (Fin.last c.val) = r := by simp [snocRows]
    have hlast' : w (prefixIndex c (Fin.last c.val)) = w c := rfl
    have hmid : ∀ i : Fin c.val, snocRows w c r i.castSucc = w (prefixIndex c i.castSucc) := by
      intro i
      simp only [snocRows, Fin.val_castSucc, i.isLt, dite_true]
      rfl
    simp only [hlast, hlast', hmid, le_refl, ite_true, not_le.mpr hx, ite_false] at h1
    omega
  have hmem := mem_orbitSet_grassSet_of_mem_bruhatCell hg c
  have h0 := evalAt_rowMinor_eq_zero_of_mem_orbitSet hT hmem
  have hshape0 : ∀ a c, a < c → kazhdanLusztigPoint w z (w a) c = 0 := fun _ _ hac =>
      kazhdanLusztigPoint_lt w z hac
  have hnum := evalAt_numMinor_of_shape w hshape0 (kazhdanLusztigPoint_self w z) r c
  rw [numMinor, evalAt_rowMinor_eq_sign c _ hS, ← hgz, h0, mul_zero, hgz,
      kazhdanLusztigPoint_free] at hnum
  exact hnum.symm

/-- **A chart point lies in `B ẇ B` iff its coordinates below the pivots vanish.** -/
theorem mem_bruhatCell_kazhdanLusztigPoint_iff (w : Equiv.Perm (Fin n)) (z : ChartVar w → K) :
    (∃ g ∈ bruhatCell K w, (g : Matrix (Fin n) (Fin n) K) = kazhdanLusztigPoint w z) ↔
      ∀ x : ChartVar w, w x.1.2 < x.1.1 → z x = 0 :=
  ⟨fun ⟨_, hg, hgz⟩ x hx => eq_zero_of_kazhdanLusztigPoint_mem_bruhatCell hg hgz x hx,
    kazhdanLusztigPoint_mem_bruhatCell w z⟩

/-- **The Kazhdan–Lusztig patch of `X_w` at `w` is the cell `C_w`.** -/
theorem kazhdanLusztigPatch_self (w : Equiv.Perm (Fin n)) :
    kazhdanLusztigPatch K w w = {z | ∀ x : ChartVar w, w x.1.2 < x.1.1 → z x = 0} := by
  ext z
  constructor
  · rintro ⟨g, hg, hgz⟩
    obtain ⟨v, hv, hgv⟩ := mem_orbitSet.mp hg
    have hwv : w ≤ᴮ v := le_of_mem_bruhatCell_of_chartMinor_ne_zero hgv fun c => by
      rw [hgz, chartMinor_kazhdanLusztigPoint]
      exact one_ne_zero
    have hvw := strongBruhat_antisymm (mem_lowerSet.mp hv) hwv
    subst hvw
    exact fun x hx => eq_zero_of_kazhdanLusztigPoint_mem_bruhatCell hgv hgz x hx
  · intro hz
    obtain ⟨g, hg, hgz⟩ := kazhdanLusztigPoint_mem_bruhatCell w z hz
    exact ⟨g, mem_orbitSet.mpr ⟨w, mem_lowerSet_self w, hg⟩, hgz⟩

/-! ### The cell as an affine space -/

/-- The point of the chart with cell coordinates `y` (other coordinates `0`). -/
def cellPoint (w : Equiv.Perm (Fin n)) (y : CellVar w → K) : Matrix (Fin n) (Fin n) K :=
  kazhdanLusztigPoint w fun x => if h : x.1.1 < w x.1.2 then y ⟨x, h⟩ else 0

theorem cellPoint_mem_bruhatCell (w : Equiv.Perm (Fin n)) (y : CellVar w → K) :
    ∃ g ∈ bruhatCell K w, (g : Matrix (Fin n) (Fin n) K) = cellPoint w y := by
  refine kazhdanLusztigPoint_mem_bruhatCell w _ fun x hx => ?_
  rw [dite_eq_right (not_lt.mpr hx.le)]

theorem ne_of_chartVar (w : Equiv.Perm (Fin n)) (x : ChartVar w) : x.1.1 ≠ w x.1.2 :=
  fun h => x.2 x.1.2 le_rfl h.symm

/-- The chart representative is invariant under right multiplication by `B`. -/
theorem chartMatrix_mul_upper (v : Equiv.Perm (Fin n)) (M b : Matrix (Fin n) (Fin n) K)
    (hb : b.IsUpperTriangular) (hbd : ∀ i, b i i ≠ 0) :
    chartMatrix K v (M * b) = chartMatrix K v M := by
  ext r c
  rw [chartMatrix_apply, chartMatrix_apply,
    evalAt_mul_of_mem_minorSpan (p := numMinor K v r c) (rowMinor_mem_minorSpan c _) M b hb,
    evalAt_mul_of_mem_minorSpan (p := chartMinor K v c) (rowMinor_mem_minorSpan c _) M b hb]
  exact mul_div_mul_left _ _ (diagPow_ne_zero hbd _)

/-- **Normal form**: every point of `B ẇ B` is `cellPoint w y · b` with `b` upper triangular. -/
theorem exists_cellPoint_mul {w : Equiv.Perm (Fin n)} {g : GL (Fin n) K}
    (hg : g ∈ bruhatCell K w) :
    ∃ (y : CellVar w → K) (b : Matrix (Fin n) (Fin n) K), b.IsUpperTriangular ∧
      (g : Matrix (Fin n) (Fin n) K) = cellPoint w y * b := by
  have hgw := evalAt_chartMinor_ne_zero_of_mem_bruhatCell hg
  obtain ⟨β, hβdef⟩ : ∃ β : GL (Fin n) K, (β : Matrix (Fin n) (Fin n) K) = chartBeta K w g :=
    ⟨unitOfDet (chartBeta K w g) (chartBeta_det_isUnit w g hgw), coe_unitOfDet _ _⟩
  have hβ : IsBorel β := by
    unfold IsBorel
    rw [hβdef]
    exact chartBeta_isUpperTriangular w (g : Matrix (Fin n) (Fin n) K)
  have hL : ((g * β : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = chartMatrix K w g := by
    rw [Units.val_mul, hβdef]
    rfl
  have hLshape := kazhdanLusztigPoint_chartMatrix w (g : Matrix (Fin n) (Fin n) K) hgw
  have hzero := eq_zero_of_kazhdanLusztigPoint_mem_bruhatCell (bruhatCell_mul_borel hg hβ)
    (hL.trans hLshape.symm)
  refine ⟨fun y => chartMatrix K w g y.1.1.1 y.1.1.2, chartInvBeta K w g, ?_, ?_⟩
  · intro i j hij
    exact chartInvBeta_blockTriangular hgw hij
  · have hcell : cellPoint w (fun y => chartMatrix K w g y.1.1.1 y.1.1.2) = chartMatrix K w g := by
      conv_rhs => rw [← hLshape]
      rw [cellPoint]
      congr 1
      funext x
      split_ifs with h
      · rfl
      · exact (hzero x (lt_of_le_of_ne (not_lt.mp h) (ne_of_chartVar w x).symm)).symm
    rw [hcell, chartMatrix_mul_chartInvBeta hgw]

/-- **Uniqueness of the normal form.** -/
theorem eq_of_cellPoint_mul {w : Equiv.Perm (Fin n)} {y y' : CellVar w → K}
    {b : Matrix (Fin n) (Fin n) K} (hb : b.IsUpperTriangular) (hbd : ∀ i, b i i ≠ 0)
    (h : cellPoint w y * b = cellPoint w y') : y = y' := by
  have h1 := congrArg (chartMatrix K w) h
  rw [chartMatrix_mul_upper w _ b hb hbd, cellPoint, cellPoint, chartMatrix_kazhdanLusztigPoint,
    chartMatrix_kazhdanLusztigPoint] at h1
  funext x
  have h2 := congrFun (congrFun h1 x.1.1.1) x.1.1.2
  rw [kazhdanLusztigPoint_free, kazhdanLusztigPoint_free, dite_eq_left x.2, dite_eq_left x.2] at h2
  exact h2

/-! ### Scheme-theoretic form on the chart: `C_w ≅ 𝔸^{ℓ(w)}` -/

/-- The vanishing ideal of a coordinate subspace is generated by the coordinates. -/
theorem vanishingIdeal_coordSubspace [Infinite K] {σ : Type*} (P : σ → Prop) :
    MvPolynomial.vanishingIdeal K {z : σ → K | ∀ x, P x → z x = 0} =
      Ideal.span (MvPolynomial.X '' {x | P x}) := by
  classical
  apply le_antisymm
  · intro p hp
    rw [MvPolynomial.mem_vanishingIdeal_iff] at hp
    let kill : MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
      MvPolynomial.aeval fun x => if P x then 0 else MvPolynomial.X x
    have hsub : p - kill p ∈ Ideal.span (MvPolynomial.X '' {x | P x}) := by
      rw [← Ideal.Quotient.eq]
      have hc : (Ideal.Quotient.mkₐ K (Ideal.span (MvPolynomial.X '' {x | P x}))).comp kill =
          Ideal.Quotient.mkₐ K _ := by
        apply MvPolynomial.algHom_ext
        intro x
        simp only [kill, AlgHom.comp_apply, MvPolynomial.aeval_X]
        split_ifs with hx
        · rw [map_zero, eq_comm, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.subset_span ⟨x, hx, rfl⟩
        · rfl
      exact (congrArg (fun φ => φ p) hc).symm
    have hkill : kill p = 0 := by
      apply MvPolynomial.funext
      intro z
      have heval : ∀ q : MvPolynomial σ K, MvPolynomial.eval z (kill q) =
          MvPolynomial.eval (fun x => if P x then 0 else z x) q := by
        intro q
        induction q using MvPolynomial.induction_on with
        | C a => simp [kill]
        | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
        | mul_X p x hp =>
          rw [map_mul, map_mul, hp, map_mul, MvPolynomial.eval_X]
          simp only [kill, MvPolynomial.aeval_X]
          split_ifs <;> simp
      rw [heval, map_zero]
      have := hp (fun x => if P x then 0 else z x) fun x hx => by simp [hx]
      simpa using this
    simpa [hkill] using hsub
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    exact MvPolynomial.mem_vanishingIdeal_iff.mpr fun z hz => by simpa using hz x hx

/-- **The patch of `X_w` at `w` is a coordinate subspace**: Fulton's minors of the generic point of
the chart `ẇ U⁻` generate the ideal of the coordinates below the pivots. -/
theorem map_kazhdanLusztigSubst_fultonIdeal_self [IsAlgClosed K] [CharZero K]
    (w : Equiv.Perm (Fin n)) :
    (fultonIdeal K w).map (kazhdanLusztigSubst K w) =
      Ideal.span ((MvPolynomial.X (R := K)) '' {x : ChartVar w | w x.1.2 < x.1.1}) := by
  rw [map_kazhdanLusztigSubst_fultonIdeal, kazhdanLusztigPatch_self, vanishingIdeal_coordSubspace]

/-- The inclusion of the cell coordinates into the chart coordinates. -/
def cellVarIncl (w : Equiv.Perm (Fin n)) : CellVar w → ChartVar w := Subtype.val

theorem cellVarIncl_injective (w : Equiv.Perm (Fin n)) : Function.Injective (cellVarIncl w) :=
  Subtype.val_injective

theorem ker_killCompl_cellVarIncl (w : Equiv.Perm (Fin n)) :
    RingHom.ker (MvPolynomial.killCompl (R := K) (cellVarIncl_injective w)).toRingHom =
      Ideal.span ((MvPolynomial.X (R := K)) '' {x : ChartVar w | w x.1.2 < x.1.1}) := by
  classical
  have hrange : ∀ x : ChartVar w, x ∈ Set.range (cellVarIncl w) ↔ x.1.1 < w x.1.2 := fun x =>
    ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  have hcompl : ∀ x : ChartVar w, ¬ x.1.1 < w x.1.2 ↔ w x.1.2 < x.1.1 := fun x =>
    ⟨fun h => lt_of_le_of_ne (not_lt.mp h) (ne_of_chartVar w x).symm, fun h => not_lt.mpr h.le⟩
  apply le_antisymm
  · intro p hp
    rw [RingHom.mem_ker] at hp
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hc : (Ideal.Quotient.mkₐ K
        (Ideal.span ((MvPolynomial.X (R := K)) '' {x : ChartVar w | w x.1.2 < x.1.1}))).comp
          ((MvPolynomial.rename (cellVarIncl w)).comp
            (MvPolynomial.killCompl (R := K) (cellVarIncl_injective w))) =
        Ideal.Quotient.mkₐ K _ := by
      apply MvPolynomial.algHom_ext
      intro x
      by_cases hx : x.1.1 < w x.1.2
      · obtain ⟨y, rfl⟩ := (hrange x).mpr hx
        simp only [AlgHom.comp_apply]
        rw [← MvPolynomial.rename_X (R := K) (cellVarIncl w) y,
          MvPolynomial.killCompl_rename_app]
      · have hz : MvPolynomial.killCompl (R := K) (cellVarIncl_injective w)
            (MvPolynomial.X x) = 0 := by
          rw [MvPolynomial.killCompl, MvPolynomial.aeval_X,
            dite_eq_right (fun h => hx ((hrange x).mp h))]
        simp only [AlgHom.comp_apply, hz, map_zero]
        rw [eq_comm, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.subset_span ⟨x, (hcompl x).mp hx, rfl⟩
    have := congrArg (fun φ => φ p) hc
    simp only [AlgHom.comp_apply] at this
    have hp' : MvPolynomial.killCompl (R := K) (cellVarIncl_injective w) p = 0 := hp
    rw [hp', map_zero, map_zero] at this
    rw [Ideal.Quotient.mkₐ_eq_mk] at this
    exact this.symm
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    change MvPolynomial.killCompl (R := K) (cellVarIncl_injective w) (MvPolynomial.X x) = 0
    rw [MvPolynomial.killCompl, MvPolynomial.aeval_X,
      dite_eq_right (fun h => (not_lt.mpr hx.le) ((hrange x).mp h))]

/-- **`C_w ≅ 𝔸^{ℓ(w)}`**: the coordinate ring of the cell (the patch of `X_w` at `w`) is a
polynomial ring in `ℓ(w)` variables. -/
def cellRingEquiv (w : Equiv.Perm (Fin n)) :
    (MvPolynomial (ChartVar w) K ⧸
      Ideal.span ((MvPolynomial.X (R := K)) '' {x : ChartVar w | w x.1.2 < x.1.1})) ≃+*
      MvPolynomial (CellVar w) K :=
  (Ideal.quotEquivOfEq (ker_killCompl_cellVarIncl w).symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := (MvPolynomial.killCompl (R := K)
      (cellVarIncl_injective w)).toRingHom) fun p =>
        ⟨MvPolynomial.rename (cellVarIncl w) p, MvPolynomial.killCompl_rename_app _ p⟩)

/-- **`dim C_w = ℓ(w)`**: the Krull dimension of the coordinate ring of the patch of `X_w` at
`w`. -/
theorem ringKrullDim_kazhdanLusztigPatch_self [IsAlgClosed K] [CharZero K]
    (w : Equiv.Perm (Fin n)) :
    ringKrullDim (MvPolynomial (ChartVar w) K ⧸ (fultonIdeal K w).map (kazhdanLusztigSubst K w)) =
      FinPermutation.length w := by
  rw [map_kazhdanLusztigSubst_fultonIdeal_self, ringKrullDim_eq_of_ringEquiv (cellRingEquiv w),
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
    zero_add, Nat.card_eq_fintype_card, card_cellVar]

end

end FlagVarieties.PointModel
