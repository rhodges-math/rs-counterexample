import Schubert.FlagVarieties.Bruhat.Dimension.Image
import Schubert.FlagVarieties.Bruhat.Cells
import Schubert.FlagVarieties.Normality.OrbitIdealComparison
import Schubert.FlagVarieties.Richardson.Schemes

/-!
# `dim X_w = ℓ(w)` for the scheme-level Schubert variety

Over an algebraically closed field `K` of characteristic `0`, for the Schubert variety
`X_w = schubertVariety K n w` (the scheme-theoretic image of `B ⟶ Fl_n`, `b ↦ b · ẇE•`):

* `isIntegral_schubertVariety`: the closed subscheme `X_w` is integral (`isIntegral_image`);
* `chartEquiv`: the coordinate ring of the big cell of `w` is the polynomial ring
  `K[ChartVar w]` of the Kazhdan–Lusztig chart, compatibly with the chart matrices
  (`universalMatrix_map_chartToPoly`);
* `specIdeal_comap_schubertVariety`: the ideal of `X_w` on the big cell chart of `w` is the image
  of the ideal `π⁻¹(X_w)` of `𝒪(GL_n)` under the section of the orbit map;
* `ringKrullDim_chart_quotient`: its quotient is the coordinate ring of the KL patch `X_w ∩ ẇU⁻`,
  which has dimension `ℓ(w)` (`ringKrullDim_kazhdanLusztigPatch_self`);
* **`topologicalKrullDim_schubertVariety`: `dim X_w = ℓ(w)`**, since the dimension of an integral
  scheme of finite type over `K` is that of any nonempty affine open
  (`topologicalKrullDim_eq_ringKrullDim`), and `X_w ∩ bigCell w` contains `ẇE•`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace FlagVarieties.Dimension

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Foundations Foundations.QuotientCharts Plucker
open PointModel (fultonIdeal kazhdanLusztigSubst kazhdanLusztigMatrix ChartVar)
open PointModel (MatrixEntryPolynomial)

universe u

variable (K : Type u) [Field K] {n : ℕ} (w : Equiv.Perm (Fin n))

/-! ### The chart ring of `w` is a polynomial ring -/

section ChartRing

theorem kazhdanLusztigMatrix_eq_perm_mul : kazhdanLusztigMatrix K w =
    (w.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) (MvPolynomial (ChartVar w) K)) *
      (kazhdanLusztigMatrix K w).submatrix w id := by
  rw [PEquiv.toMatrix_toPEquiv_mul, Matrix.submatrix_submatrix]
  ext r c
  simp

theorem isLowerUnitriangular_kazhdanLusztigMatrix :
    IsLowerUnitriangular ((kazhdanLusztigMatrix K w).submatrix w id) := by
  refine ⟨fun i c hic => ?_, fun i => ?_⟩
  · have hic' : i < c := OrderDual.toDual_lt_toDual.mp hic
    simp only [Matrix.submatrix_apply, id, kazhdanLusztigMatrix]
    split_ifs with h1 h2
    · exact absurd rfl (h1 i hic'.le)
    · exact absurd (w.injective h2) hic'.ne
    · rfl
  · simp only [Matrix.submatrix_apply, id, kazhdanLusztigMatrix]
    split_ifs with h1
    · exact absurd rfl (h1 i le_rfl)
    · rfl

theorem isUnit_det_kazhdanLusztigMatrix : IsUnit (kazhdanLusztigMatrix K w).det := by
  rw [kazhdanLusztigMatrix_eq_perm_mul]
  exact isUnit_det_perm_mul w (isLowerUnitriangular_kazhdanLusztigMatrix K w)

theorem inBigCell_kazhdanLusztigMatrix : InBigCell w
    (matrixFlag (kazhdanLusztigMatrix K w) (isUnit_det_kazhdanLusztigMatrix K w)) := by
  have h := inBigCell_matrixFlag_perm_mul w (isLowerUnitriangular_kazhdanLusztigMatrix K w)
  rwa [matrixFlag_congr (kazhdanLusztigMatrix_eq_perm_mul K w).symm
      _ (isUnit_det_kazhdanLusztigMatrix K w)] at h

/-- The coordinates of the big cell of `w`. -/
def chartToPoly : bigCellRing K w →ₐ[K] MvPolynomial (ChartVar w) K :=
  bigCellPoint K (inBigCell_kazhdanLusztigMatrix K w)

theorem universalMatrix_map_chartToPoly :
    (bigCellUniversalMatrix K w).map (chartToPoly K w) = kazhdanLusztigMatrix K w := by
  rw [chartToPoly, map_bigCellPoint (R := K) w]
  exact (bigCellMatrix_eq_of_perm_mul _ (isLowerUnitriangular_kazhdanLusztigMatrix K w)
    (matrixFlag_congr (kazhdanLusztigMatrix_eq_perm_mul K w).symm _ _)).trans
        (kazhdanLusztigMatrix_eq_perm_mul K w).symm

/-- The inverse: the chart coordinate `z_rc` is the entry `(r, c)` of the chart matrix. -/
def polyToChart : MvPolynomial (ChartVar w) K →ₐ[K] bigCellRing K w :=
  MvPolynomial.aeval fun x => bigCellUniversalMatrix K w x.1.1 x.1.2

theorem chartToPoly_comp_polyToChart :
    (chartToPoly K w).comp (polyToChart K w) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro x
  rw [AlgHom.comp_apply, polyToChart, MvPolynomial.aeval_X, AlgHom.id_apply]
  have := congrFun (congrFun (universalMatrix_map_chartToPoly K w) x.1.1) x.1.2
  rw [Matrix.map_apply] at this
  rw [this]
  simp only [kazhdanLusztigMatrix]
  rw [dite_eq_left x.2]
  rfl

theorem polyToChart_comp_chartToPoly :
    (polyToChart K w).comp (chartToPoly K w) = AlgHom.id K _ := by
  apply bigCellRing_algHom_ext w
  rw [← map_map_algHom, universalMatrix_map_chartToPoly]
  obtain ⟨u, hu, he⟩ := bigCellMatrix_eq_perm_mul (inBigCell_bigCellUniversalFlag K w)
  have hL : bigCellUniversalMatrix K w = (w.symm.toPEquiv.toMatrix : Matrix _ _ _) * u := he
  ext r c
  simp only [Matrix.map_apply, AlgHom.id_apply]
  simp only [kazhdanLusztigMatrix]
  split_ifs with h1 h2
  · rw [polyToChart, MvPolynomial.aeval_X]
  · rw [map_one, hL, PEquiv.toMatrix_toPEquiv_mul, Matrix.submatrix_apply, id, h2,
      Equiv.symm_apply_apply, hu.2 c]
  · rw [map_zero, hL, PEquiv.toMatrix_toPEquiv_mul, Matrix.submatrix_apply, id]
    obtain ⟨j, hjc, hj⟩ : ∃ j ≤ c, w j = r := by simpa using h1
    have hjs : w.symm r = j := by rw [← hj, Equiv.symm_apply_apply]
    have hjc' : j < c := lt_of_le_of_ne hjc fun e => h2 (by rw [← hj, e])
    rw [hjs]
    exact (hu.1 (OrderDual.toDual_lt_toDual.mpr hjc')).symm

/-- **The big cell of `w` is the affine space of the KL chart**. -/
def chartEquiv : bigCellRing K w ≃ₐ[K] MvPolynomial (ChartVar w) K :=
  AlgEquiv.ofAlgHom (chartToPoly K w) (polyToChart K w) (chartToPoly_comp_polyToChart K w)
    (polyToChart_comp_chartToPoly K w)

/-- The section of the orbit map, read in the chart, is the KL substitution. -/
theorem chartToPoly_comp_section :
    (chartToPoly K w).comp ((bigCellSectionComorphism K w).comp
      (IsScalarTower.toAlgHom K (MatrixEntryPolynomial K n) (GLCoord K n))) =
          kazhdanLusztigSubst K w := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  rw [AlgHom.comp_apply, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', ← genericMatrix_apply_eq,
    PointModel.kazhdanLusztigSubst, MvPolynomial.aeval_X]
  have h1 := congrFun (congrFun (genericMatrix_map_glPointOfMatrix K _
    (isUnit_det_bigCellMatrix (inBigCell_bigCellUniversalFlag K w))) i) j
  rw [Matrix.map_apply] at h1
  rw [h1]
  have h2 := congrFun (congrFun (universalMatrix_map_chartToPoly K w) i) j
  rw [Matrix.map_apply] at h2
  exact h2

/-- **The KL patch of `X_w` at `w` in the chart has dimension `ℓ(w)`.** -/
theorem ringKrullDim_chart_quotient [IsAlgClosed K] [CharZero K] :
    ringKrullDim (bigCellRing K w ⧸ (preimageIdeal K n (schubertVariety K n w)).map
      (bigCellSectionComorphism K w).toRingHom) = Schubert.FinPermutation.length w := by
  rw [preimageIdeal_schubertVariety_eq_schubertOrbitIdeal K n w,
    PointModel.schubertOrbitIdeal_eq_orbitIdeal_lowerSet,
    PointModel.orbitIdeal_lowerSet_eq_fultonIdeal, Ideal.map_map]
  have hJ : (fultonIdeal K w).map (kazhdanLusztigSubst K w).toRingHom =
      ((fultonIdeal K w).map (((bigCellSectionComorphism K w).toRingHom).comp
        (algebraMap (MatrixEntryPolynomial K n) (GLCoord K n)))).map
          ((chartEquiv K w).toRingEquiv : bigCellRing K w →+* MvPolynomial (ChartVar w) K) := by
    rw [Ideal.map_map]
    congr 1
    rw [← chartToPoly_comp_section K w]
    rfl
  rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ (chartEquiv K w).toRingEquiv hJ)]
  exact PointModel.ringKrullDim_kazhdanLusztigPatch_self w

end ChartRing

/-! ### The Schubert scheme -/

section Scheme

/-- **The Schubert variety `X_w` is an integral scheme.** -/
theorem isIntegral_schubertVariety : IsIntegral (schubertVariety K n w).subscheme :=
  isIntegral_image (schubertOrbitMap K n w)

/-- The structure morphism of `X_w`. -/
abbrev schubertToSpec : (schubertVariety K n w).subscheme ⟶ Spec (CommRingCat.of K) :=
  (schubertVariety K n w).subschemeι ≫ FlagScheme.toSpec K n

/-- The image of the big cell chart of `w`, an affine open of `Fl_n`. -/
abbrev bigCellAffine : (FlagScheme K n).affineOpens :=
  ⟨specChart K n w ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion _⟩

theorem specChart_eq :
    specChart K n w = Spec.map (CommRingCat.ofHom (bigCellSectionComorphism K w).toRingHom) ≫
      (TauCeti.GeneralLinear.groupSchemeSpecIso K n).inv ≫ FlagScheme.orbitMap K n := by
  rw [specChart, ← bigCellSection_orbitMap]
  change (Spec.map (CommRingCat.ofHom (bigCellSectionComorphism K w).toRingHom) ≫
    (TauCeti.GeneralLinear.groupSchemeSpecIso K n).inv) ≫ FlagScheme.orbitMap K n = _
  rw [Category.assoc]

/-- **The ideal of `X_w` on the big cell chart of `w`.** -/
theorem specIdeal_comap_schubertVariety :
    specIdeal ((schubertVariety K n w).comap (specChart K n w)) =
      (preimageIdeal K n (schubertVariety K n w)).map
        (bigCellSectionComorphism K w).toRingHom := by
  have := isAffine_glScheme K n
  rw [specChart_eq, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp,
    specIdeal_comap_spec_map]
  congr 1
  rw [specIdeal, ideal_top_comap_of_isIso, IsIso.Iso.inv_inv, Ideal.comap_comap]
  rfl

theorem ringKrullDim_bigCellAffine [IsAlgClosed K] [CharZero K] :
    ringKrullDim (Γ(FlagScheme K n, (bigCellAffine K w).1) ⧸
      (schubertVariety K n w).ideal (bigCellAffine K w)) = Schubert.FinPermutation.length w := by
  have h1 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion (schubertVariety K n w)
    (specChart K n w) ⟨⊤, isAffineOpen_top _⟩
  let E := ((specChart K n w).appIso ⊤).commRingCatIsoToRingEquiv
  have hJ : ((schubertVariety K n w).comap (specChart K n w)).ideal ⟨⊤, isAffineOpen_top _⟩ =
      ((schubertVariety K n w).ideal (bigCellAffine K w)).map E := by
    rw [h1, ← Ideal.comap_symm]
    rfl
  let E2 := (Scheme.ΓSpecIso (CommRingCat.of (bigCellRing K w))).commRingCatIsoToRingEquiv
  have hJ2 : specIdeal ((schubertVariety K n w).comap (specChart K n w)) =
      (((schubertVariety K n w).comap (specChart K n w)).ideal ⟨⊤, isAffineOpen_top _⟩).map E2 := by
    rw [specIdeal, ← Ideal.comap_symm]
    rfl
  rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ E hJ),
    ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ E2 hJ2),
    specIdeal_comap_schubertVariety]
  exact ringKrullDim_chart_quotient K w

/-- The point `ẇE•` lies on `X_w` over the big cell of `w`. -/
theorem exists_mem_bigCellAffine :
    (((schubertVariety K n w).subschemeι ⁻¹ᵁ (bigCellAffine K w).1 :
      (schubertVariety K n w).subscheme.Opens) :
        Set (schubertVariety K n w).subscheme).Nonempty := by
  let p : Spec (CommRingCat.of K) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  have hsupp : permFlag K n w p ∈ ((schubertVariety K n w).support : Set (FlagScheme K n)) :=
    Scheme.IdealSheafData.support_antitone (Richardson.schubertVariety_le_ker_permFlag_self K w)
      ((permFlag K n w).range_subset_ker_support ⟨p, rfl⟩)
  rw [← Scheme.IdealSheafData.range_subschemeι] at hsupp
  obtain ⟨y, hy⟩ := hsupp
  refine ⟨y, ?_⟩
  change (schubertVariety K n w).subschemeι y ∈ specChart K n w ''ᵁ ⊤
  rw [hy, Scheme.Hom.image_top_eq_opensRange]
  have hP := inBigCell_matrixFlag_perm_mul (A := K) w Richardson.isLowerUnitriangular_one
  obtain ⟨g, hg⟩ := exists_factor_of_inBigCell (R := K) w _ hP
  have he : permFlag K n w = g ≫ specChart K n w := by
    rw [Richardson.permFlag_eq_ofRingFlag, specChart, hg]
    congr 1
    exact matrixFlag_congr (by rw [mul_one]; rfl) _ _
  rw [he]
  exact ⟨g p, rfl⟩

/-- **`dim X_w = ℓ(w)`**: the Schubert variety `X_w ⊆ Fl_n` has dimension the length of `w`. -/
theorem topologicalKrullDim_schubertVariety [IsAlgClosed K] [CharZero K] :
    topologicalKrullDim (schubertVariety K n w).subscheme = Schubert.FinPermutation.length w := by
  have := isIntegral_schubertVariety K w
  have hW : IsAffineOpen ((schubertVariety K n w).subschemeι ⁻¹ᵁ (bigCellAffine K w).1) := by
    rw [← Scheme.IdealSheafData.opensRange_subschemeCover_map]
    exact isAffineOpen_opensRange _
  rw [topologicalKrullDim_eq_ringKrullDim (schubertToSpec K w) hW (exists_mem_bigCellAffine K w),
    ringKrullDim_eq_of_ringEquiv
      ((schubertVariety K n w).subschemeObjIso (bigCellAffine K w)).commRingCatIsoToRingEquiv]
  exact ringKrullDim_bigCellAffine K w

end Scheme

end FlagVarieties.Dimension
