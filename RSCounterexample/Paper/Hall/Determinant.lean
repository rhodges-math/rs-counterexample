import RSCounterexample.Paper.Hall.Admissible
import RSCounterexample.Paper.DoubleSourceExtraction
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# The Hall coefficient-extraction identity

Lemma 3.1 of the paper (`lem:hall-determinant`). Let `x_1, …, x_d, t_1, …, t_m` be variables,
`0 ≤ ℓ_1 ≤ ⋯ ≤ ℓ_m`, and `R_i = {t_j : ℓ_j ≥ i}`. Then

`[x_1 ⋯ x_d] Δ_d(x) ∏_j ∏_{i ≤ ℓ_j} (1 − x_i t_j)^{−1} = det(h_{1+i−j}(R_i)) = ∑ t_{j_1} ⋯ t_{j_d}`,

the sum over the Hall-admissible subsets `{j_1 < ⋯ < j_d}`. Rows `R_i` may be empty.

In Lean the coefficients live in an arbitrary commutative ring `R` containing the `t_j`, and each
geometric series is truncated in degree `B ≥ d`, which does not change the coefficient of
`x_1 ⋯ x_d` (`hall_determinant`).

The first equality is the Vandermonde step (`source_extraction_determinant`). The second is the
flagged column identity of the library (`hall_source_extraction`, proved with a lattice-path
involution, for nonempty rows), reindexed to Hall-admissible subsets; when some row is empty,
both sides vanish.

## Main definitions

* `Schubert.RS.Hall.hallProduct ℓ t B`: `Δ_d(x) ∏_j ∏_{i ≤ ℓ_j} ∑_{a ≤ B} (x_i t_j)^a`.
* `Schubert.RS.Hall.completeH p t q`: `h_q` of the variables `t_j` with `p j`.
* `Schubert.RS.Hall.hallMatrix ℓ t`: the matrix `(h_{1+i−j}(R_i))`.
* `Schubert.RS.Hall.hallSum ℓ t`: the sum over the Hall-admissible subsets.
-/

namespace Schubert.RS.Hall

open MvPolynomial

noncomputable section

variable {R : Type*} [CommRing R] {d m : ℕ}

/-! ### The three expressions -/

/-- The geometric series `∑_{a ≤ B} (x_i t)^a` in the variables `x_0, …, x_{d−1}`, truncated in
degree `B`. -/
def geomTerm (i : Fin d) (t : R) (B : ℕ) : AddMonoidAlgebra R (Weight d) :=
  ∑ a : Fin (B + 1), AddMonoidAlgebra.single (Pi.single i (a.val : ℤ)) (t ^ a.val)

/-- `Δ_d(x) ∏_j ∏_{i ≤ ℓ_j} (1 − x_i t_j)^{−1}`, each geometric series truncated in degree `B`
(positions `0`-based: `x_i` with `i < ℓ_j`). -/
def hallProduct (ℓ : Fin m → ℕ) (t : Fin m → R) (B : ℕ) : AddMonoidAlgebra R (Weight d) :=
  AddMonoidAlgebra.mapRingHom (Weight d) (Int.castRingHom R) (weylFactor d) *
    ∏ j : Fin m, ∏ i ∈ Finset.univ.filter (fun i : Fin d => i.val < ℓ j), geomTerm i (t j) B

/-- The complete homogeneous polynomial `h_q` of the variables `t_j` with `p j`, evaluated in
`R`; it is zero in negative degree. -/
def completeH (p : Fin m → Prop) [DecidablePred p] (t : Fin m → R) (q : ℤ) : R :=
  if 0 ≤ q then aeval (fun j : {j : Fin m // p j} => t j) (hsymm {j : Fin m // p j} ℤ q.toNat)
  else 0

/-- The matrix `(h_{1+i−j}(R_i))_{i,j}` with `R_i = {t_j : ℓ_j ≥ i}` (row `i` of the paper is
row `i − 1` here). -/
def hallMatrix (ℓ : Fin m → ℕ) (t : Fin m → R) : Matrix (Fin d) (Fin d) R :=
  fun i j => completeH (fun j' => i.val < ℓ j') t (1 + i.val - j.val)

/-- The sum of `t_{j_1} ⋯ t_{j_d}` over the Hall-admissible subsets. -/
def hallSum (ℓ : Fin m → ℕ) (t : Fin m → R) : R :=
  ∑ J ∈ Finset.univ.filter (IsHallAdmissible (d := d) ℓ), ∏ k, t (J k)

/-! ### Grouping the factors by rows -/

/-- Row `i`: `∏_{j : ℓ_j > i} ∑_{a ≤ B} (x t_j)^a` as a one-variable Laurent polynomial. -/
def hallRow (ℓ : Fin m → ℕ) (t : Fin m → R) (B : ℕ) (i : Fin d) : AddMonoidAlgebra R ℤ :=
  finiteSlotProduct (fun j : {j : Fin m // i.val < ℓ j} => t j) B

theorem sourceRow_eq_mapDomainRingHom (i : Fin d) (p : AddMonoidAlgebra R ℤ) :
    sourceRow i p =
      AddMonoidAlgebra.mapDomainRingHom R (AddMonoidHom.single (fun _ : Fin d => ℤ) i) p :=
  rfl

theorem prod_geomTerm_eq (ℓ : Fin m → ℕ) (t : Fin m → R) (B : ℕ) :
    ∏ j : Fin m, ∏ i ∈ Finset.univ.filter (fun i : Fin d => i.val < ℓ j), geomTerm i (t j) B =
      ∏ i : Fin d, sourceRow i (hallRow ℓ t B i) := by
  classical
  have h1 : ∏ j : Fin m, ∏ i ∈ Finset.univ.filter (fun i : Fin d => i.val < ℓ j),
      geomTerm i (t j) B =
      ∏ i : Fin d, ∏ j ∈ Finset.univ.filter (fun j : Fin m => i.val < ℓ j), geomTerm i (t j) B := by
    simp only [Finset.prod_filter]
    exact Finset.prod_comm
  rw [h1]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [sourceRow_eq_mapDomainRingHom, hallRow, finiteSlotProduct, map_prod,
    Finset.prod_subtype (Finset.univ.filter (fun j : Fin m => i.val < ℓ j))
      (p := fun j => i.val < ℓ j) (by simp)]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [geomTerm, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single]
  rfl

/-! ### Coefficients of the rows -/

/-- The exponent vectors of total degree `k` and the multisets of size `k`. -/
def expEquivSym {ι : Type*} [Fintype ι] [DecidableEq ι] (B k : ℕ) (hk : k ≤ B) :
    {e : ι → Fin (B + 1) // ∑ h, (e h).val = k} ≃ Sym ι k where
  toFun e := ⟨Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm fun h => (e.val h).val), by
    rw [Finsupp.card_toMultiset, Finsupp.sum_fintype _ _ (fun _ => rfl)]
    simpa using e.2⟩
  invFun s := ⟨fun h => ⟨(s : Multiset ι).count h, by
      have h1 : (s : Multiset ι).count h ≤ Multiset.card (s : Multiset ι) :=
        Multiset.count_le_card h _
      rw [Sym.card_coe] at h1
      omega⟩, by
    simp only
    rw [Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a), Sym.card_coe]⟩
  left_inv e := by
    apply Subtype.ext
    funext h
    apply Fin.ext
    simp [Finsupp.count_toMultiset]
  right_inv s := by
    apply Sym.ext
    ext a
    simp [Finsupp.count_toMultiset]

theorem aeval_hsymm_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → R) (k : ℕ) :
    aeval f (hsymm ι ℤ k) = ∑ s : Sym ι k, ((s : Multiset ι).map f).prod := by
  rw [hsymm, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_multiset_prod, Multiset.map_map]
  congr 1
  exact Multiset.map_congr rfl fun a _ => aeval_X f a

/-- In degrees `0 ≤ k ≤ B` the truncated geometric product has the coefficients of `h_k`. -/
theorem finiteSlotProduct_coeff_hsymm {ι : Type*} [Fintype ι] [DecidableEq ι] (slot : ι → R)
    (B k : ℕ) (hk : k ≤ B) :
    (finiteSlotProduct slot B).coeff (k : ℤ) = aeval slot (hsymm ι ℤ k) := by
  rw [finiteSlotProduct_natural, aeval_hsymm_eq_sum]
  refine Fintype.sum_equiv (expEquivSym B k hk) _ _ fun e => ?_
  change _ = ((Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm fun h => (e.val h).val) :
    Multiset ι).map slot).prod
  rw [Finset.prod_multiset_map_count]
  symm
  rw [Finset.prod_subset (Finset.subset_univ _) (fun h _ hh => by
    rw [Multiset.count_eq_zero.mpr (by simpa using hh), pow_zero])]
  refine Finset.prod_congr rfl fun h _ => ?_
  rw [Finsupp.count_toMultiset, Finsupp.coe_equivFunOnFinite_symm]

theorem hallRow_coeff (ℓ : Fin m → ℕ) (t : Fin m → R) (B : ℕ) (i : Fin d) (q : ℤ)
    (hq : q ≤ B) :
    (hallRow ℓ t B i).coeff q = completeH (fun j' => i.val < ℓ j') t q := by
  classical
  unfold completeH hallRow
  split_ifs with h0
  · have hq' : q = (q.toNat : ℤ) := (Int.toNat_of_nonneg h0).symm
    rw [hq', finiteSlotProduct_coeff_hsymm _ B q.toNat (by omega), Int.toNat_natCast]
  · exact finiteSlotProduct_negative _ B (by omega)

/-- **The first equality of Lemma 3.1**: the extracted coefficient is `det(h_{1+i−j}(R_i))`. -/
theorem hallProduct_coeff_eq_det (ℓ : Fin m → ℕ) (t : Fin m → R) (B : ℕ) (hB : d ≤ B) :
    (hallProduct (d := d) ℓ t B).coeff (fun _ => 1) = (hallMatrix (d := d) ℓ t).det := by
  rw [hallProduct, prod_geomTerm_eq, source_extraction_determinant]
  congr 1
  funext i j
  exact hallRow_coeff ℓ t B i _ (by have := i.isLt; have := j.isLt; omega)

/-! ### The second equality -/

/-- `|R_{i+1}| = #{j : ℓ_j > i}`. -/
def rowCount (ℓ : Fin m → ℕ) (i : ℕ) : ℕ := (Finset.univ.filter fun j : Fin m => i < ℓ j).card

theorem rowCount_le (ℓ : Fin m → ℕ) (i : ℕ) : rowCount ℓ i ≤ m := by
  unfold rowCount
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- For weakly increasing heights, `{j : ℓ_j > i}` is the final segment of `Fin m` of size
`|R_{i+1}|`. -/
theorem lt_iff_rowCount_le (ℓ : Fin m → ℕ) (hℓ : Monotone ℓ) (i : ℕ) (j : Fin m) :
    i < ℓ j ↔ m - rowCount ℓ i ≤ j.val := by
  classical
  set S := Finset.univ.filter fun j : Fin m => i < ℓ j with hS
  by_cases hne : S.Nonempty
  · have hIci : S = Finset.Ici (S.min' hne) := by
      ext j'
      rw [Finset.mem_Ici]
      constructor
      · intro hj'
        exact Finset.min'_le S j' hj'
      · intro hj'
        have h1 := (Finset.mem_filter.mp (Finset.min'_mem S hne)).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1.trans_le (hℓ hj')⟩
    have hcard : rowCount ℓ i = m - (S.min' hne).val := by
      change S.card = _
      rw [congrArg Finset.card hIci, Fin.card_Ici]
    have hlt := (S.min' hne).isLt
    have hmem : i < ℓ j ↔ S.min' hne ≤ j := by
      rw [← Finset.mem_Ici, ← hIci]
      simp [hS]
    rw [hmem, Fin.le_def, hcard]
    omega
  · have hcard : rowCount ℓ i = 0 := by
      change S.card = 0
      exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne)
    rw [hcard, Nat.sub_zero]
    constructor
    · intro hj
      exact absurd ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩ hne
    · intro hj
      exact absurd j.isLt (by omega)

theorem rowCount_antitone (ℓ : Fin m → ℕ) {i i' : ℕ} (h : i ≤ i') :
    rowCount ℓ i' ≤ rowCount ℓ i :=
  Finset.card_le_card fun j hj => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    omega

section Nonempty

variable {M : ℕ} (ℓ : Fin (M + 1) → ℕ) (t : Fin (M + 1) → R)

/-- The slots of the flagged column: `y_r = t_{m+1−r}`. -/
def revSlot : Fin (M + 1) → R := fun h => t (Fin.rev h)

/-- The flag `b_k = #{j : ℓ_j ≥ d + 1 − k}`, shifted down by one. -/
def flagHeights (hpos : ∀ i < d, 0 < rowCount ℓ i) : Fin d → Fin (M + 1) := fun k =>
  ⟨rowCount ℓ (d - 1 - k.val) - 1, by
    have := hpos (d - 1 - k.val) (by omega)
    have := rowCount_le ℓ (d - 1 - k.val)
    omega⟩

theorem flagHeights_monotone (hpos : ∀ i < d, 0 < rowCount ℓ i) :
    Monotone fun k => (flagHeights (d := d) ℓ hpos k).val := by
  intro k k' hkk'
  have h1 := rowCount_antitone ℓ (show d - 1 - k'.val ≤ d - 1 - k.val by
    have : k.val ≤ k'.val := hkk'
    omega)
  simp only [flagHeights]
  omega

omit [CommRing R] in
theorem val_rev_mk {n : ℕ} (a : ℕ) (h : a < n) : (Fin.rev (⟨a, h⟩ : Fin n)).val = n - (a + 1) :=
  Fin.val_rev _

/-- The rows of the Hall product are the rows of the flagged column with reversed slots. -/
theorem hallRow_eq_flagSourceRow (hℓ : Monotone ℓ) (hpos : ∀ i < d, 0 < rowCount ℓ i) (B : ℕ)
    (i : Fin d) :
    hallRow ℓ t B i = flagSourceRow (flagHeights ℓ hpos) (revSlot t) B i := by
  have hc := hpos i.val i.isLt
  have hcm := rowCount_le ℓ i.val
  have hy : (flagHeights (d := d) ℓ hpos i.rev).val = rowCount ℓ i.val - 1 := by
    simp only [flagHeights, Fin.val_rev]
    congr 2
    omega
  let e : Fin ((flagHeights ℓ hpos i.rev).val + 1) ≃ {j : Fin (M + 1) // i.val < ℓ j} :=
    { toFun := fun h => ⟨Fin.rev ⟨h.val, by have := h.isLt; omega⟩, by
        rw [lt_iff_rowCount_le ℓ hℓ, val_rev_mk]
        have := h.isLt
        omega⟩
      invFun := fun j => ⟨(Fin.rev j.val).val, by
        have hj := (lt_iff_rowCount_le ℓ hℓ i.val j.val).mp j.2
        rw [Fin.val_rev]
        have := j.val.isLt
        omega⟩
      left_inv := fun h => by
        apply Fin.ext
        simp only [Fin.rev_rev]
      right_inv := fun j => by
        apply Subtype.ext
        apply Fin.ext
        dsimp only
        rw [val_rev_mk, Fin.val_rev]
        have := j.val.isLt
        omega }
  unfold hallRow flagSourceRow finiteSlotProduct
  exact (Fintype.prod_equiv e _ _ fun h => rfl).symm

/-- The strictly increasing flagged columns and the Hall-admissible subsets. -/
def strictHeightsEquiv (hℓ : Monotone ℓ) (hpos : ∀ i < d, 0 < rowCount ℓ i) :
    HallLattice.StrictHeights (flagHeights (d := d) ℓ hpos) ≃
      {J : Fin d → Fin (M + 1) // IsHallAdmissible ℓ J} where
  toFun r := ⟨fun k => Fin.rev ⟨(r.val k.rev).val, by
      have := (r.val k.rev).isLt
      have := (flagHeights (d := d) ℓ hpos k.rev).isLt
      omega⟩, by
    refine ⟨fun k k' hkk' => ?_, fun k => ?_⟩
    · have h : (r.val k'.rev).val < (r.val k.rev).val := r.2 (Fin.rev_lt_rev.mpr hkk')
      have := (r.val k.rev).isLt
      have := (flagHeights (d := d) ℓ hpos k.rev).isLt
      rw [Fin.lt_def, val_rev_mk, val_rev_mk]
      omega
    · have hb := (r.val k.rev).isLt
      have hc := rowCount_le ℓ k.val
      have hk := hpos k.val k.isLt
      have hy : (flagHeights (d := d) ℓ hpos k.rev).val = rowCount ℓ k.val - 1 := by
        simp only [flagHeights, Fin.val_rev]
        congr 2
        have := k.isLt
        omega
      rw [Nat.add_one_le_iff, lt_iff_rowCount_le ℓ hℓ, val_rev_mk]
      omega⟩
  invFun J := ⟨fun i => ⟨(Fin.rev (J.val i.rev)).val, by
      have hadm := J.2.2 i.rev
      have hj := (lt_iff_rowCount_le ℓ hℓ i.rev.val (J.val i.rev)).mp (by omega)
      have hy : (flagHeights (d := d) ℓ hpos i).val = rowCount ℓ i.rev.val - 1 := by
        simp only [flagHeights, Fin.val_rev]
        congr 2
        omega
      have := (J.val i.rev).isLt
      rw [Fin.val_rev, hy]
      omega⟩, fun i i' hii' => by
    have h := J.2.1 (Fin.rev_lt_rev.mpr hii')
    rw [Fin.lt_def] at h
    have := (J.val i.rev).isLt
    have := (J.val i'.rev).isLt
    show (Fin.rev (J.val i.rev)).val < (Fin.rev (J.val i'.rev)).val
    rw [Fin.val_rev, Fin.val_rev]
    omega⟩
  left_inv r := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    have key : ∀ i' : Fin d, i' = i → (r.val i').val = (r.val i).val := by
      rintro _ rfl
      rfl
    dsimp only
    rw [Fin.rev_rev (n := M + 1)]
    exact key _ (Fin.rev_rev i)
  right_inv J := by
    apply Subtype.ext
    funext k
    apply Fin.ext
    dsimp only
    rw [val_rev_mk, Fin.val_rev, Fin.rev_rev]
    have := (J.val k).isLt
    omega

theorem hallSum_eq_hallPolynomial (hℓ : Monotone ℓ) (hpos : ∀ i < d, 0 < rowCount ℓ i) :
    hallSum (d := d) ℓ t = hallPolynomial (flagHeights ℓ hpos) (revSlot t) := by
  rw [hallSum, Finset.sum_subtype (Finset.univ.filter (IsHallAdmissible (d := d) ℓ))
    (p := IsHallAdmissible ℓ) (by simp), hallPolynomial]
  refine (Fintype.sum_equiv (strictHeightsEquiv ℓ hℓ hpos) _ _ fun r => ?_).symm
  simp only [strictHeightsEquiv, Equiv.coe_fn_mk, revSlot]
  refine Fintype.prod_equiv Fin.revPerm _ _ fun i => ?_
  have key : ∀ i' : Fin d, i' = i → ∀ (h : (r.val i).val < M + 1) (h' : (r.val i').val < M + 1),
      t (Fin.rev ⟨(r.val i).val, h⟩) = t (Fin.rev ⟨(r.val i').val, h'⟩) := by
    rintro _ rfl _ _
    rfl
  exact key _ (by simp) _ _

end Nonempty

theorem completeH_empty {p : Fin m → Prop} [DecidablePred p] (hp : ∀ j, ¬ p j) (t : Fin m → R)
    {q : ℤ} (hq : 0 < q) : completeH p t q = 0 := by
  unfold completeH
  rw [ite_eq_left (by omega), aeval_hsymm_eq_sum]
  have : IsEmpty (Sym {j : Fin m // p j} q.toNat) := ⟨fun s => by
    obtain ⟨a, _⟩ := Multiset.card_pos_iff_exists_mem.mp
      (show 0 < Multiset.card (s : Multiset {j : Fin m // p j}) by rw [Sym.card_coe]; omega)
    exact hp a.val a.2⟩
  simp

/-- **The second equality of Lemma 3.1**: `det(h_{1+i−j}(R_i))` is the sum over the
Hall-admissible subsets. -/
theorem hallMatrix_det_eq_hallSum (ℓ : Fin m → ℕ) (hℓ : Monotone ℓ) (t : Fin m → R) :
    (hallMatrix (d := d) ℓ t).det = hallSum (d := d) ℓ t := by
  classical
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [Matrix.det_isEmpty, hallSum,
      Finset.filter_true_of_mem fun J _ => ⟨fun a _ _ => a.elim0, fun k => k.elim0⟩]
    simp
  by_cases hne : ∃ j : Fin m, d ≤ ℓ j
  · obtain ⟨j₀, hj₀⟩ := hne
    obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, by have := j₀.isLt; omega⟩
    have hpos : ∀ i < d, 0 < rowCount ℓ i := fun i hi =>
      Finset.card_pos.mpr ⟨j₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩
    rw [← hallProduct_coeff_eq_det ℓ t d le_rfl, hallSum_eq_hallPolynomial ℓ t hℓ hpos,
      hallProduct, prod_geomTerm_eq]
    simp only [hallRow_eq_flagSourceRow ℓ t hℓ hpos d]
    exact hall_source_extraction _ (flagHeights_monotone ℓ hpos) _ d le_rfl
  · have hrow : ∀ j : Fin d, hallMatrix (d := d) ℓ t ⟨d - 1, by omega⟩ j = 0 := fun j =>
      completeH_empty (fun j' h => hne ⟨j', by simp only at h; omega⟩) t
        (by have := j.isLt; simp only; omega)
    rw [Matrix.det_eq_zero_of_row_eq_zero _ hrow, hallSum]
    refine (Finset.sum_eq_zero fun J hJ => ?_).symm
    have h := (Finset.mem_filter.mp hJ).2.2 ⟨d - 1, by omega⟩
    exact absurd ⟨J ⟨d - 1, by omega⟩, by simp only at h; omega⟩ hne

/-- **Lemma 3.1 of the paper** (`lem:hall-determinant`). For weakly increasing heights `ℓ` and any
truncation degree `B ≥ d`,
`[x_1 ⋯ x_d] Δ_d(x) ∏_j ∏_{i ≤ ℓ_j} (1 − x_i t_j)^{−1} = det(h_{1+i−j}(R_i))` and
`det(h_{1+i−j}(R_i)) = ∑ t_{j_1} ⋯ t_{j_d}` over the Hall-admissible subsets. -/
theorem hall_determinant (ℓ : Fin m → ℕ) (hℓ : Monotone ℓ) (t : Fin m → R) (B : ℕ)
    (hB : d ≤ B) :
    (hallProduct (d := d) ℓ t B).coeff (fun _ => 1) = (hallMatrix (d := d) ℓ t).det ∧
      (hallMatrix (d := d) ℓ t).det = hallSum (d := d) ℓ t :=
  ⟨hallProduct_coeff_eq_det ℓ t B hB, hallMatrix_det_eq_hallSum ℓ hℓ t⟩

end

end Schubert.RS.Hall
