import Schubert.FlagVarieties.PointModel.VanishingIdeals
import Schubert.FlagVarieties.PointModel.RankTransfer
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Transfer of the standard-monomial inputs to fields of characteristic `0`

The restriction of a polynomial to the orbit `U ẇ` is a polynomial `orbitPoly K w p` in the entries
above the diagonal of a generic unitriangular matrix. It is defined over `ℚ` and commutes with
extension of scalars (`map_orbitPoly`). Taking coefficients on a fixed finite set of monomials, the
restrictions of the standard products `colProd K h T` become the images of fixed rational vectors
(`coordMap_colProd`), so that:

* `finrank_vanishSpan_add_finrank_span`: `dim (I_S^A ∩ A_h) + rank = dim A_h` over every infinite
  field, where `rank` is the rank of these rational vectors;
* `PointModel.StandardMonomialTheory.transfer` (**transfer**): if the standard-monomial inputs hold
  over one field of characteristic `0` (e.g. `ℂ`, from the Demazure library), they hold over every
  field of characteristic `0`.
-/

open Schubert Demazure.FlagModule Demazure.SchubertUnions FinPermutation Module

namespace FlagVarieties.PointModel

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {n : ℕ}

/-! ### Orbit polynomials -/

/-- The generic upper unitriangular matrix, with entries `X (i, k)` above the diagonal. -/
def genUni (K : Type*) [Field K] (n : ℕ) : Matrix (Fin n) (Fin n) (MatrixEntryPolynomial K n) :=
  fun i k => if i = k then 1 else if i < k then MvPolynomial.X (i, k) else 0

/-- The restriction of `p` to the orbit `U ẇ`, as a polynomial in the entries of `u ∈ U`. -/
def orbitPoly (K : Type*) [Field K] (w : Equiv.Perm (Fin n)) :
    MatrixEntryPolynomial K n →ₐ[K] MatrixEntryPolynomial K n :=
  MvPolynomial.aeval fun ij => genUni K n ij.1 (w ij.2)

/-- The upper unitriangular matrix with entries `y` above the diagonal. -/
def uniOf (y : Fin n × Fin n → K) : Matrix (Fin n) (Fin n) K :=
  fun i k => if i = k then 1 else if i < k then y (i, k) else 0

theorem isUnitriangular_uniOf (y : Fin n × Fin n → K) : IsUnitriangular (uniOf y) := by
  refine ⟨fun i k hki => ?_, fun i => by simp [uniOf]⟩
  have h1 : i ≠ k := (ne_of_lt hki).symm
  have h2 : ¬ i < k := not_lt.mpr hki.le
  simp [uniOf, h1, h2]

theorem eq_uniOf {u : Matrix (Fin n) (Fin n) K} (hu : IsUnitriangular u) :
    u = uniOf fun ik => u ik.1 ik.2 := by
  ext i k
  simp only [uniOf]
  split_ifs with h1 h2
  · rw [h1, hu.2]
  · rfl
  · exact hu.1 (lt_of_le_of_ne (not_lt.mp h2) (Ne.symm h1))

theorem eval_orbitPoly (w : Equiv.Perm (Fin n)) (y : Fin n × Fin n → K)
    (p : MatrixEntryPolynomial K n) :
    MvPolynomial.eval y (orbitPoly K w p) = evalAt (uniOf y * permMat K w) p := by
  have hc : (MvPolynomial.aeval y).comp (orbitPoly K w) = evalAt (uniOf y * permMat K w) := by
    refine MvPolynomial.algHom_ext fun ij => ?_
    rw [AlgHom.comp_apply, orbitPoly, MvPolynomial.aeval_X, evalAt_X, mul_permMat]
    simp only [genUni, uniOf]
    split_ifs <;> simp
  have := DFunLike.congr_fun hc p
  rw [AlgHom.comp_apply] at this
  exact this

theorem orbitPoly_eq_zero_iff [Infinite K] (w : Equiv.Perm (Fin n))
    (p : MatrixEntryPolynomial K n) :
    orbitPoly K w p = 0 ↔
      ∀ u : Matrix (Fin n) (Fin n) K, IsUnitriangular u → evalAt (u * permMat K w) p = 0 := by
  constructor
  · intro h u hu
    rw [eq_uniOf hu, ← eval_orbitPoly, h, map_zero]
  · intro h
    refine MvPolynomial.funext fun y => ?_
    rw [eval_orbitPoly, map_zero]
    exact h _ (isUnitriangular_uniOf y)

/-! ### Extension of scalars from `ℚ` -/

variable (E : Type*) [Field E] [CharZero E]

/-- Extension of scalars `ℚ[x_ij] → E[x_ij]`. -/
abbrev ratMap : MatrixEntryPolynomial ℚ n →+* MatrixEntryPolynomial E n :=
    MvPolynomial.map (algebraMap ℚ E)

theorem ratMap_rowMinor (k : Fin n) (s : Fin (k.val + 1) → Fin n) :
    ratMap E (rowMinor ℚ k s) = rowMinor E k s := by
  rw [rowMinor, rowMinor, RingHom.map_det]
  congr 1
  ext i j
  simp [RingHom.mapMatrix_apply]

theorem ratMap_colProd {d : ℕ} (h : Fin d → Fin n) (T : (j : Fin d) → FlagMinorRowSet (h j)) :
    ratMap E (colProd ℚ h T) = colProd E h T := by
  rw [colProd, colProd, map_prod]
  exact Finset.prod_congr rfl fun j _ => ratMap_rowMinor E _ _

theorem ratMap_orbitPoly (w : Equiv.Perm (Fin n)) (p : MatrixEntryPolynomial ℚ n) :
    ratMap E (orbitPoly ℚ w p) = orbitPoly E w (ratMap E p) := by
  have : (ratMap E).comp (orbitPoly ℚ w).toRingHom =
      (orbitPoly E w).toRingHom.comp (ratMap E) := by
    refine MvPolynomial.ringHom_ext (fun q => ?_) (fun ij => ?_)
    · simp [orbitPoly]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, orbitPoly,
        MvPolynomial.aeval_X, MvPolynomial.map_X, genUni]
      split_ifs <;> simp
  exact congrArg (fun f => f p) this

/-! ### Coordinates on a finite set of monomials -/

variable {d : ℕ} (h : Fin d → Fin n)

/-- The monomials occurring in the orbit restrictions of the standard products of shape `h`. -/
def monos : Finset ((Fin n × Fin n) →₀ ℕ) := by
  classical exact Finset.univ.biUnion fun w : Equiv.Perm (Fin n) =>
    Finset.univ.biUnion fun T : (j : Fin d) → FlagMinorRowSet (h j) =>
      (orbitPoly ℚ w (colProd ℚ h T)).support

/-- The rational coordinate vector of the restriction of a standard product to the orbits of `S`. -/
def ratCoords (S : Finset (Equiv.Perm (Fin n))) (T : (j : Fin d) → FlagMinorRowSet (h j)) :
    {w // w ∈ S} × monos h → ℚ :=
  fun x => (orbitPoly ℚ x.1.1 (colProd ℚ h T)).coeff x.2.1

/-- The coordinates of the orbit restrictions over `E`. -/
def coordMap (S : Finset (Equiv.Perm (Fin n))) :
    MatrixEntryPolynomial E n →ₗ[E] ({w // w ∈ S} × monos h → E) where
  toFun p x := (orbitPoly E x.1.1 p).coeff x.2.1
  map_add' p q := by
    funext x
    simp
  map_smul' c p := by
    funext x
    simp

theorem coordMap_colProd (S : Finset (Equiv.Perm (Fin n)))
    (T : (j : Fin d) → FlagMinorRowSet (h j)) :
    coordMap E h S (colProd E h T) = ratVec E (ratCoords h S T) := by
  funext x
  change (orbitPoly E x.1.1 (colProd E h T)).coeff x.2.1 = algebraMap ℚ E _
  rw [← ratMap_colProd E h T, ← ratMap_orbitPoly, MvPolynomial.coeff_map]
  rfl

theorem support_orbitPoly_subset {p : MatrixEntryPolynomial E n} (hp : p ∈ flagSpan E h)
    (w : Equiv.Perm (Fin n)) :
    (orbitPoly E w p).support ⊆ monos h := by
  classical
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨T, rfl⟩ := hp
    rw [← ratMap_colProd E h T, ← ratMap_orbitPoly]
    intro μ hμ
    have hμ' := MvPolynomial.support_map_subset _ _ hμ
    simp only [monos, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨w, T, hμ'⟩
  | zero => simp
  | add p q _ _ hp hq =>
    rw [map_add]
    exact MvPolynomial.support_add.trans (Finset.union_subset hp hq)
  | smul c p _ hp =>
    rw [map_smul]
    exact MvPolynomial.support_smul.trans hp

theorem coordMap_eq_zero_iff (S : Finset (Equiv.Perm (Fin n))) {p : MatrixEntryPolynomial E n}
    (hp : p ∈ flagSpan E h) :
    coordMap E h S p = 0 ↔ ∀ w ∈ S, orbitPoly E w p = 0 := by
  constructor
  · intro h0 w hw
    ext μ
    rw [show (0 : MatrixEntryPolynomial E n).coeff μ = 0 by simp]
    by_cases hμ : μ ∈ monos h
    · exact congrFun h0 (⟨w, hw⟩, ⟨μ, hμ⟩)
    · by_contra hne
      exact hμ (support_orbitPoly_subset E h hp w (MvPolynomial.mem_support_iff.mpr hne))
  · intro h0
    funext x
    change (orbitPoly E x.1.1 p).coeff x.2.1 = 0
    rw [h0 x.1.1 x.1.2]
    simp

theorem mem_vanishSpan_iff_coordMap (S : Finset (Equiv.Perm (Fin n)))
    {p : MatrixEntryPolynomial E n}
    (hp : p ∈ flagSpan E h) :
    p ∈ vanishSpan E (columnMultiplicity h) S ↔ coordMap E h S p = 0 := by
  have : Infinite E := Infinite.of_injective (Nat.cast : ℕ → E) Nat.cast_injective
  have hp' : p ∈ minorSpan E (columnMultiplicity h) := by
    rw [minorSpan_columnMultiplicity]
    exact hp
  rw [coordMap_eq_zero_iff E h S hp]
  constructor
  · intro hv w hw
    rw [orbitPoly_eq_zero_iff]
    exact (forall_mem_orbitSet_iff hp' S).mp hv.2 w hw
  · intro h0
    refine ⟨hp', (forall_mem_orbitSet_iff hp' S).mpr fun w hw => ?_⟩
    exact (orbitPoly_eq_zero_iff w p).mp (h0 w hw)

/-- `dim (I_S^A ∩ A_h) + rank = dim A_h`, over every field of characteristic `0`. -/
theorem finrank_vanishSpan_add_finrank_span (S : Finset (Equiv.Perm (Fin n))) :
    finrank E (vanishSpan E (columnMultiplicity h) S) +
      finrank E (Submodule.span E (Set.range fun T => ratVec E (ratCoords h S T))) =
        finrank E (flagSpan E h) := by
  let f := (coordMap E h S).comp (flagSpan E h).subtype
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  have hr :
      LinearMap.range f = Submodule.span E (Set.range fun T => ratVec E (ratCoords h S T)) := by
    rw [LinearMap.range_comp, Submodule.range_subtype, flagSpan, Submodule.map_span,
      ← Set.range_comp, show ⇑(coordMap E h S) ∘ colProd E h = fun T => ratVec E (ratCoords h S T)
        from funext fun T => coordMap_colProd E h S T]
  have hk :
      LinearMap.ker f = (vanishSpan E (columnMultiplicity h) S).comap (flagSpan E h).subtype := by
    ext p
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype,
      mem_vanishSpan_iff_coordMap E h S p.2]
    rfl
  have hk' : finrank E (LinearMap.ker f) = finrank E (vanishSpan E (columnMultiplicity h) S) := by
    have hle : vanishSpan E (columnMultiplicity h) S ≤ flagSpan E h := fun p hp => by
      rw [← minorSpan_columnMultiplicity]
      exact hp.1
    rw [hk, (Submodule.equivMapOfInjective _ (flagSpan E h).injective_subtype _).finrank_eq,
      Submodule.map_comap_subtype, inf_eq_right.mpr hle]
  rw [hr, hk'] at hrn
  omega

theorem coordMap_sum (S : Finset (Equiv.Perm (Fin n)))
    (c : ((j : Fin d) → FlagMinorRowSet (h j)) → E) :
    coordMap E h S (∑ T, c T • colProd E h T) = ∑ T, c T • ratVec E (ratCoords h S T) := by
  rw [map_sum]
  simp only [map_smul, coordMap_colProd]

omit [CharZero E] in
theorem sum_smul_colProd_mem (c : ((j : Fin d) → FlagMinorRowSet (h j)) → E) :
    ∑ T, c T • colProd E h T ∈ flagSpan E h :=
  Submodule.sum_mem _ fun T _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨T, rfl⟩)

/-! ### The transfer -/

/-- **Transfer of the standard-monomial inputs** between fields of characteristic `0`. -/
theorem StandardMonomialTheory.transfer (F : Type*) [Field F] [CharZero F]
    (hE : StandardMonomialTheory E) :
    StandardMonomialTheory F := by
  refine ⟨fun {n d} h {S} hS => ?_, fun {n d} h {v w} hvw p hp hw => ?_⟩
  · have hdimE := hE.dim h hS
    have hE' := finrank_vanishSpan_add_finrank_span E h S
    have hF' := finrank_vanishSpan_add_finrank_span F h S
    have r1 := finrank_span_algebraMap_comp E (ratCoords h S)
    have r2 := finrank_span_algebraMap_comp F (ratCoords h S)
    omega
  · have : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
    have : Infinite E := Infinite.of_injective (Nat.cast : ℕ → E) Nat.cast_injective
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hp
    have hsumE : ∀ c : ((j : Fin d) → FlagMinorRowSet (h j)) → E,
        ∑ T, c T • ratVec E (ratCoords h {w} T) = 0 →
          ∑ T, c T • ratVec E (ratCoords h {v} T) = 0 := by
      intro c hc
      have hmem := sum_smul_colProd_mem E h c
      rw [← coordMap_sum] at hc ⊢
      rw [coordMap_eq_zero_iff E h _ hmem] at hc ⊢
      intro v' hv'
      rw [Finset.mem_singleton] at hv'
      subst hv'
      rw [orbitPoly_eq_zero_iff]
      exact hE.closure h hvw _ hmem
        ((orbitPoly_eq_zero_iff w _).mp (hc w (Finset.mem_singleton_self w)))
    have hwF : ∑ T, c T • ratVec F (ratCoords h {w} T) = 0 := by
      rw [← coordMap_sum, coordMap_eq_zero_iff F h _ hp]
      intro w' hw'
      rw [Finset.mem_singleton] at hw'
      subst hw'
      exact (orbitPoly_eq_zero_iff w' _).mpr hw
    have hvF := ker_le_of_ker_le E F (ratCoords h {w}) (ratCoords h {v}) hsumE c hwF
    rw [← coordMap_sum, coordMap_eq_zero_iff F h _ hp] at hvF
    exact (orbitPoly_eq_zero_iff v _).mp (hvF v (Finset.mem_singleton_self v))

end

end FlagVarieties.PointModel
