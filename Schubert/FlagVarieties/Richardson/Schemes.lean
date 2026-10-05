import Schubert.FlagVarieties.Richardson.Basic
import Schubert.FlagVarieties.Plucker.OrbitMapCoordinates
import Schubert.FlagVarieties.Bruhat.Schemes

/-!
# Richardson varieties and torus-fixed points at the scheme level

For the ideal sheaves `X_w = schubertVariety R n w`, `X^v = oppositeSchubertVariety R n v` and
`X_w^v = richardsonVariety R n w v` on `Fl_n`, using the Plücker morphisms:

* On the orbit maps `b ↦ b · ẇE•` of `B` and `B⁻`, the Plücker coordinate `X_T` of height `k` is
  identically zero when `T ≰ w{0..k}` (for `B`), resp. `v{0..k} ≰ T` (for `B⁻`), in the Gale order
  (`schubertOrbitMap_preimage_chart`, `oppSchubertOrbitMap_preimage_chart`). So the support of `X_w`
  (resp. `X^v`) avoids the open set `plucker⁻¹ D₊(X_T)` (`support_schubertVariety_subset`,
  `support_oppositeSchubertVariety_subset`).
* **`richardsonVariety_eq_top`** (any commutative ring): if `v ≰ w`, then `X_w ∩ X^v = ∅`.
* **`richardsonVariety_ne_top_iff`** (a field of characteristic `0`): `X_w ∩ X^v ≠ ∅ ⟺ v ≤ w`;
  for `v ≤ w` the `T`-fixed point `v̇E•` lies in `X_w ∩ X^v`.
* **Torus-fixed points**: `schubertVariety_le_ker_permFlag_iff` (characteristic `0`):
  `u̇E• ∈ X_w ⟺ u ≤ w`; `le_of_oppositeSchubertVariety_le_ker_permFlag`: `u̇E• ∈ X^v → v ≤ u`;
  `le_of_richardsonVariety_le_ker_permFlag`: `u̇E• ∈ X_w ∩ X^v → v ≤ u ≤ w`.

Membership `u̇E• ∈ X^v` for `v < u` (the opposite closure relation) is proved in
`Richardson/Translation.lean`, by translation with `w₀`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace FlagVarieties.Richardson

open AlgebraicGeometry CategoryTheory
open Foundations Foundations.QuotientCharts Demazure.FlagModule Plucker
open PointModel (galeLE galeLE_of_rows_le strongBruhat_iff_galeLE schubertVariety_le_iff)

universe u

variable {n : ℕ}

/-! ### Flag minors of `b ẇ` -/

section Minors

variable {A : Type*} [CommRing A]

theorem minor_mul_permMatrix (b : Matrix (Fin n) (Fin n) A) (w : Equiv.Perm (Fin n)) {k : Fin n}
    (T : FlagMinorRowSet k) :
    minor (b * permMatrix (A := A) n w) T =
      (Equiv.Perm.sign (flagPrefixPermutation w k) : A) *
        (b.submatrix T.rows (flagPrefixRows w k).rows).det := by
  rw [minor, ← Matrix.det_permute']
  congr 1
  ext i j
  simp only [permMatrix, PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_apply, id,
    Equiv.symm_symm, flagPrefixPermutation_spec]

/-- For `b` lower triangular, `Δ_T(b ẇ) = 0` unless `w{0..k} ≤ T`. -/
theorem minor_mul_permMatrix_eq_zero_of_lower {b : Matrix (Fin n) (Fin n) A}
    (hb : b.BlockTriangular OrderDual.toDual) (w : Equiv.Perm (Fin n)) {k : Fin n}
    {T : FlagMinorRowSet k} (hT : ¬ galeLE (flagPrefixRows w k) T) :
    minor (b * permMatrix (A := A) n w) T = 0 := by
  rw [minor_mul_permMatrix, ← Matrix.det_transpose, Matrix.transpose_submatrix,
    upperTriangular_minor_zero b.transpose
      (fun i j hij => hb (show OrderDual.toDual i < OrderDual.toDual j from hij)) _ _
      (fun h => hT (galeLE_of_rows_le h)), mul_zero]

/-- For `b` upper triangular, `Δ_T(b ẇ) = 0` unless `T ≤ w{0..k}`. -/
theorem minor_mul_permMatrix_eq_zero_of_upper {b : Matrix (Fin n) (Fin n) A}
    (hb : b.BlockTriangular id) (w : Equiv.Perm (Fin n)) {k : Fin n}
    {T : FlagMinorRowSet k} (hT : ¬ galeLE T (flagPrefixRows w k)) :
    minor (b * permMatrix (A := A) n w) T = 0 := by
  rw [minor_mul_permMatrix, upperTriangular_minor_zero b hb _ _
    (fun h => hT (galeLE_of_rows_le h)), mul_zero]

end Minors

/-! ### The orbit maps as flags of matrices -/

variable (R : Type u) [CommRing R]

theorem isUnit_det_borel_mul_permMatrix (w : Equiv.Perm (Fin n)) :
    IsUnit (borelMatrix R n * permMatrix (A := BorelCoord R n) n w).det := by
  rw [Matrix.det_mul]
  exact (isUnit_det_borelMatrix R n).mul (isUnit_det_permMatrix n w)

theorem isUnit_det_oppBorel_mul_permMatrix (w : Equiv.Perm (Fin n)) :
    IsUnit (oppBorelMatrix R n * permMatrix (A := OppBorelCoord R n) n w).det := by
  rw [Matrix.det_mul]
  exact (isUnit_det_map_ringHom _
    (TauCeti.GeneralLinear.isUnit_det_localizedGenericMatrix R n)).mul (isUnit_det_permMatrix n w)

/-- The orbit map `B ⟶ Fl_n`, `b ↦ b · ẇE•`, is the flag of `b ẇ`. -/
theorem schubertOrbitMap_eq (w : Equiv.Perm (Fin n)) :
    schubertOrbitMap R n w = FlagScheme.ofRingFlag R
      (matrixFlag (borelMatrix R n * permMatrix n w) (isUnit_det_borel_mul_permMatrix R w)) := by
  have h1 : borelInclusion R n = GLScheme.point R n (Ideal.Quotient.mkₐ R (borelCoordIdeal R n)) :=
      rfl
  rw [schubertOrbitMap, h1]
  refine (FlagScheme.orbitMapAt_point (permRingFlag n w R) (permFlag_toSpec R n w) _).trans ?_
  congr 1
  rw [permRingFlag_baseChange, permRingFlag_eq_matrixFlag]
  apply matrixFlag_transport
  rfl

/-- The orbit map `B⁻ ⟶ Fl_n`, `b ↦ b · ẇE•`, is the flag of `b ẇ`. -/
theorem oppSchubertOrbitMap_eq (w : Equiv.Perm (Fin n)) :
    oppSchubertOrbitMap R n w = FlagScheme.ofRingFlag R
      (matrixFlag (oppBorelMatrix R n * permMatrix n w)
        (isUnit_det_oppBorel_mul_permMatrix R w)) := by
  have h1 : oppBorelInclusion R n =
      GLScheme.point R n (Ideal.Quotient.mkₐ R (oppBorelIdeal R n)) := rfl
  rw [oppSchubertOrbitMap, h1]
  refine (FlagScheme.orbitMapAt_point (permRingFlag n w R) (permFlag_toSpec R n w) _).trans ?_
  congr 1
  rw [permRingFlag_baseChange, permRingFlag_eq_matrixFlag]
  apply matrixFlag_transport
  rfl

/-! ### Vanishing Plücker coordinates on the orbits -/

theorem schubertOrbitMap_preimage_chart (w : Equiv.Perm (Fin n)) {k : Fin n}
    {T : FlagMinorRowSet k} (hT : ¬ galeLE T (flagPrefixRows w k)) :
    (schubertOrbitMap R n w ≫ plucker R n k) ⁻¹ᵁ chart R (FlagMinorRowSet k) T = ⊥ := by
  rw [schubertOrbitMap_eq, ofRingFlag_plucker, fromSections_preimage_chart]
  simp only [specSections]
  rw [minor_mul_permMatrix_eq_zero_of_upper (borelMatrix_blockTriangular R n) w hT, map_zero,
    Scheme.basicOpen_zero]

theorem oppSchubertOrbitMap_preimage_chart (v : Equiv.Perm (Fin n)) {k : Fin n}
    {T : FlagMinorRowSet k} (hT : ¬ galeLE (flagPrefixRows v k) T) :
    (oppSchubertOrbitMap R n v ≫ plucker R n k) ⁻¹ᵁ chart R (FlagMinorRowSet k) T = ⊥ := by
  rw [oppSchubertOrbitMap_eq, ofRingFlag_plucker, fromSections_preimage_chart]
  simp only [specSections]
  rw [minor_mul_permMatrix_eq_zero_of_lower (oppBorelMatrix_blockTriangular R n) v hT, map_zero,
    Scheme.basicOpen_zero]

/-- If `X_T` vanishes on `f`, the support of the scheme-theoretic image of `f` avoids
`plucker⁻¹ D₊(X_T)`. -/
theorem support_ker_subset {Y : Scheme.{u}} (f : Y ⟶ FlagScheme R n) [QuasiCompact f] {k : Fin n}
    (T : FlagMinorRowSet k) (h : (f ≫ plucker R n k) ⁻¹ᵁ chart R (FlagMinorRowSet k) T = ⊥) :
    (f.ker.support : Set (FlagScheme R n)) ⊆
      ((plucker R n k ⁻¹ᵁ chart R (FlagMinorRowSet k) T : (FlagScheme R n).Opens) : Set _)ᶜ := by
  rw [Scheme.Hom.support_ker]
  refine closure_minimal ?_ (plucker R n k ⁻¹ᵁ chart R (FlagMinorRowSet k) T).isOpen.isClosed_compl
  rintro _ ⟨y, rfl⟩ hy
  have hy' : y ∈ (f ≫ plucker R n k) ⁻¹ᵁ chart R (FlagMinorRowSet k) T := by
    rw [Scheme.Hom.comp_preimage]
    exact hy
  rw [h] at hy'
  exact hy'

theorem support_schubertVariety_subset (w : Equiv.Perm (Fin n)) {k : Fin n}
    {T : FlagMinorRowSet k} (hT : ¬ galeLE T (flagPrefixRows w k)) :
    ((schubertVariety R n w).support : Set (FlagScheme R n)) ⊆
      ((plucker R n k ⁻¹ᵁ chart R (FlagMinorRowSet k) T : (FlagScheme R n).Opens) : Set _)ᶜ :=
  support_ker_subset R _ T (schubertOrbitMap_preimage_chart R w hT)

theorem support_oppositeSchubertVariety_subset (v : Equiv.Perm (Fin n)) {k : Fin n}
    {T : FlagMinorRowSet k} (hT : ¬ galeLE (flagPrefixRows v k) T) :
    ((oppositeSchubertVariety R n v).support : Set (FlagScheme R n)) ⊆
      ((plucker R n k ⁻¹ᵁ chart R (FlagMinorRowSet k) T : (FlagScheme R n).Opens) : Set _)ᶜ :=
  support_ker_subset R _ T (oppSchubertOrbitMap_preimage_chart R v hT)

/-- Every point of `Fl_n` lies in some chart `plucker⁻¹ D₊(X_{u{0..k}})`. -/
theorem exists_mem_preimage_chart (x : FlagScheme R n) (k : Fin n) :
    ∃ u : Equiv.Perm (Fin n),
      x ∈ plucker R n k ⁻¹ᵁ chart R (FlagMinorRowSet k) (flagPrefixRows u k) := by
  obtain ⟨u, hu⟩ := exists_mem_bigCell R x
  obtain ⟨y, rfl⟩ := Scheme.Hom.mem_opensRange.mp hu
  refine ⟨u, ?_⟩
  have htop : (specChart R n u ≫ plucker R n k) ⁻¹ᵁ
      chart R (FlagMinorRowSet k) (flagPrefixRows u k) = ⊤ := by
    rw [specChart_plucker, chartMorphism, fromSections_preimage_chart]
    apply Scheme.basicOpen_of_isUnit
    obtain ⟨u', hu', he⟩ := bigCellMatrix_eq_perm_mul (inBigCell_bigCellUniversalFlag R u)
    rw [chartSections, chartMatrix, bigCellUniversalMatrix, he]
    exact (isUnit_minor_perm_mul u hu' k).map _
  have hy : y ∈ (specChart R n u ≫ plucker R n k) ⁻¹ᵁ
      chart R (FlagMinorRowSet k) (flagPrefixRows u k) := by
    rw [htop]
    trivial
  rw [Scheme.Hom.comp_preimage] at hy
  exact hy

/-! ### Nonemptiness -/

/-- **If `v ≰ w`, the Richardson variety `X_w ∩ X^v` is empty** (over any commutative ring). -/
theorem richardsonVariety_eq_top {w v : Equiv.Perm (Fin n)} (h : ¬ v ≤ᴮ w) :
    richardsonVariety R n w v = ⊤ := by
  obtain ⟨k, hk⟩ : ∃ k, ¬ galeLE (flagPrefixRows v k) (flagPrefixRows w k) := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact h (strongBruhat_iff_galeLE.mpr hall)
  rw [← Scheme.IdealSheafData.support_eq_bot_iff, richardsonVariety,
    Scheme.IdealSheafData.support_sup, eq_bot_iff]
  intro x hx
  have hx' : x ∈ ((schubertVariety R n w).support : Set (FlagScheme R n)) ∩
      (oppositeSchubertVariety R n v).support := by
    rwa [← TopologicalSpace.Closeds.coe_inf]
  exfalso
  obtain ⟨u, hu⟩ := exists_mem_preimage_chart R x k
  by_cases hTw : galeLE (flagPrefixRows u k) (flagPrefixRows w k)
  · have hvT : ¬ galeLE (flagPrefixRows v k) (flagPrefixRows u k) := fun hvT => hk (hvT.trans hTw)
    exact support_oppositeSchubertVariety_subset R v hvT hx'.2 hu
  · exact support_schubertVariety_subset R w hTw hx'.1 hu

/-! ### Torus-fixed points -/

theorem isLowerUnitriangular_one {A : Type*} [CommRing A] :
    IsLowerUnitriangular (1 : Matrix (Fin n) (Fin n) A) :=
  ⟨Matrix.blockTriangular_one, fun i => Matrix.one_apply_eq i⟩

/-- The `T`-fixed point `u̇E•` lies in the chart `plucker⁻¹ D₊(X_{u{0..k}})`. -/
theorem permFlag_preimage_chart (u : Equiv.Perm (Fin n)) (k : Fin n) :
    (permFlag R n u ≫ plucker R n k) ⁻¹ᵁ chart R (FlagMinorRowSet k) (flagPrefixRows u k) = ⊤ := by
  rw [permFlag, permRingFlag_eq_matrixFlag, ofRingFlag_plucker, fromSections_preimage_chart]
  apply Scheme.basicOpen_of_isUnit
  have h := isUnit_minor_perm_mul (A := R) u isLowerUnitriangular_one k
  rw [mul_one] at h
  exact h.map _

theorem permFlag_mem_support [Nontrivial R] {I : (FlagScheme R n).IdealSheafData}
    (u : Equiv.Perm (Fin n)) (h : I ≤ (permFlag R n u).ker) :
    ∃ x, x ∈ (I.support : Set (FlagScheme R n)) ∧
      ∀ k, x ∈ plucker R n k ⁻¹ᵁ chart R (FlagMinorRowSet k) (flagPrefixRows u k) := by
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum R) := inferInstance
  refine ⟨permFlag R n u p, Scheme.IdealSheafData.support_antitone h
    ((permFlag R n u).range_subset_ker_support ⟨p, rfl⟩), fun k => ?_⟩
  have hp : p ∈ (permFlag R n u ≫ plucker R n k) ⁻¹ᵁ
      chart R (FlagMinorRowSet k) (flagPrefixRows u k) := by
    rw [permFlag_preimage_chart]
    trivial
  rw [Scheme.Hom.comp_preimage] at hp
  exact hp

/-- **`u̇E• ∈ X_w → u ≤ w`** (over a nonzero ring). -/
theorem le_of_schubertVariety_le_ker_permFlag [Nontrivial R] {w u : Equiv.Perm (Fin n)}
    (h : schubertVariety R n w ≤ (permFlag R n u).ker) : u ≤ᴮ w := by
  obtain ⟨x, hx, hxk⟩ := permFlag_mem_support R u h
  refine strongBruhat_iff_galeLE.mpr fun k => ?_
  by_contra hk
  exact support_schubertVariety_subset R w hk hx (hxk k)

/-- **`u̇E• ∈ X^v → v ≤ u`** (over a nonzero ring). -/
theorem le_of_oppositeSchubertVariety_le_ker_permFlag [Nontrivial R] {v u : Equiv.Perm (Fin n)}
    (h : oppositeSchubertVariety R n v ≤ (permFlag R n u).ker) : v ≤ᴮ u := by
  obtain ⟨x, hx, hxk⟩ := permFlag_mem_support R u h
  refine strongBruhat_iff_galeLE.mpr fun k => ?_
  by_contra hk
  exact support_oppositeSchubertVariety_subset R v hk hx (hxk k)

/-- **`u̇E• ∈ X_w ∩ X^v → v ≤ u ≤ w`.** -/
theorem le_of_richardsonVariety_le_ker_permFlag [Nontrivial R] {w v u : Equiv.Perm (Fin n)}
    (h : richardsonVariety R n w v ≤ (permFlag R n u).ker) : v ≤ᴮ u ∧ u ≤ᴮ w :=
  ⟨le_of_oppositeSchubertVariety_le_ker_permFlag R (le_sup_right.trans h),
    le_of_schubertVariety_le_ker_permFlag R (le_sup_left.trans h)⟩

/-- The identity of `B⁻`. -/
def oppBorelOne : OppBorelCoord R n →ₐ[R] R :=
  Ideal.Quotient.liftₐ (oppBorelIdeal R n) (glPointOfMatrix R (1 : Matrix (Fin n) (Fin n) R)
    (by rw [Matrix.det_one]; exact isUnit_one)) (by
      have hle : oppBorelIdeal R n ≤ RingHom.ker
          (glPointOfMatrix R (1 : Matrix (Fin n) (Fin n) R)
            (by rw [Matrix.det_one]; exact isUnit_one)).toRingHom := by
        rw [oppBorelIdeal, Ideal.span_le]
        rintro _ ⟨⟨⟨i, j⟩, hij⟩, rfl⟩
        have h := congrFun (congrFun (genericMatrix_map_glPointOfMatrix R
          (1 : Matrix (Fin n) (Fin n) R) (by rw [Matrix.det_one]; exact isUnit_one)) i) j
        simp only [Matrix.map_apply] at h
        simp only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
          AlgHom.coe_toRingHom, h]
        exact Matrix.one_apply_ne (ne_of_lt hij)
      exact fun a ha => hle ha)

theorem oppBorelMatrix_map_oppBorelOne :
    (oppBorelMatrix R n).map (oppBorelOne R) = 1 := by
  ext i j
  exact congrFun (congrFun (genericMatrix_map_glPointOfMatrix R (1 : Matrix (Fin n) (Fin n) R)
    (by rw [Matrix.det_one]; exact isUnit_one)) i) j

/-- The identity of `B`. -/
abbrev borelOne : BorelCoord R n →ₐ[R] R :=
  borelPointOfMatrix R (1 : Matrix (Fin n) (Fin n) R) (by rw [Matrix.det_one]; exact isUnit_one)
    Matrix.blockTriangular_one

theorem permFlag_eq_ofRingFlag (u : Equiv.Perm (Fin n)) :
    permFlag R n u = FlagScheme.ofRingFlag R
      (matrixFlag (permMatrix (A := R) n u) (isUnit_det_permMatrix n u)) := by
  rw [permFlag, permRingFlag_eq_matrixFlag]

/-- **`u̇E• ∈ X_u`**: the `T`-fixed point is the orbit map at the identity of `B`. -/
theorem schubertVariety_le_ker_permFlag_self (u : Equiv.Perm (Fin n)) :
    schubertVariety R n u ≤ (permFlag R n u).ker := by
  have he : Spec.map (CommRingCat.ofHom (borelOne R (n := n)).toRingHom) ≫ schubertOrbitMap R n u =
      permFlag R n u := by
    rw [schubertOrbitMap_point, permFlag_eq_ofRingFlag]
    congr 1
    apply matrixFlag_congr
    rw [borelMatrix_map_borelPointOfMatrix, one_mul]
  rw [← he]
  exact Scheme.Hom.le_ker_comp _ _

/-- **`v̇E• ∈ X^v`**. -/
theorem oppositeSchubertVariety_le_ker_permFlag_self (v : Equiv.Perm (Fin n)) :
    oppositeSchubertVariety R n v ≤ (permFlag R n v).ker := by
  let _ : Algebra (OppBorelCoord R n) R := (oppBorelOne R (n := n)).toRingHom.toAlgebra
  have _ : @IsScalarTower R (OppBorelCoord R n) R Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun r => ((oppBorelOne R (n := n)).commutes r).symm
  have he : Spec.map (CommRingCat.ofHom (algebraMap (OppBorelCoord R n) R)) ≫
      oppSchubertOrbitMap R n v = permFlag R n v := by
    rw [oppSchubertOrbitMap_eq, FlagScheme.ofRingFlag_baseChange,
      matrixFlag_map _ _ (isUnit_det_map _ (isUnit_det_oppBorel_mul_permMatrix R v)),
      permFlag_eq_ofRingFlag]
    congr 1
    apply matrixFlag_congr
    rw [Matrix.map_mul, permMatrix, permMatrix_map]
    change (oppBorelMatrix R n).map (oppBorelOne R) * _ = _
    rw [oppBorelMatrix_map_oppBorelOne, one_mul]
    rfl
  rw [← he]
  exact Scheme.Hom.le_ker_comp _ _

/-! ### Over a field of characteristic `0` -/

variable (K : Type u) [Field K] [CharZero K]

/-- **`u̇E• ∈ X_w ⟺ u ≤ w`** (characteristic `0`). -/
theorem schubertVariety_le_ker_permFlag_iff {w u : Equiv.Perm (Fin n)} :
    schubertVariety K n w ≤ (permFlag K n u).ker ↔ u ≤ᴮ w :=
  ⟨le_of_schubertVariety_le_ker_permFlag K, fun h =>
    (schubertVariety_le_iff.mpr h).trans (schubertVariety_le_ker_permFlag_self K u)⟩

/-- For `v ≤ w`, the `T`-fixed point `v̇E•` lies in `X_w ∩ X^v`. -/
theorem richardsonVariety_le_ker_permFlag {w v : Equiv.Perm (Fin n)} (h : v ≤ᴮ w) :
    richardsonVariety K n w v ≤ (permFlag K n v).ker :=
  sup_le ((schubertVariety_le_ker_permFlag_iff K).mpr h)
    (oppositeSchubertVariety_le_ker_permFlag_self K v)

omit [CharZero K] in
theorem ker_permFlag_ne_top (u : Equiv.Perm (Fin n)) : (permFlag K n u).ker ≠ ⊤ := by
  intro htop
  have := (Scheme.Hom.ker_eq_top_iff_isEmpty _).mp htop
  exact this.false (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)

/-- **`X_w ∩ X^v ≠ ∅ ⟺ v ≤ w`** (characteristic `0`). -/
theorem richardsonVariety_ne_top_iff {w v : Equiv.Perm (Fin n)} :
    richardsonVariety K n w v ≠ ⊤ ↔ v ≤ᴮ w := by
  constructor
  · intro h
    by_contra hvw
    exact h (richardsonVariety_eq_top K hvw)
  · intro h htop
    apply ker_permFlag_ne_top K v
    exact top_le_iff.mp (htop ▸ richardsonVariety_le_ker_permFlag K h)

end FlagVarieties.Richardson
