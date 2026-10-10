import RSCounterexample.FlagVarieties.Schubert.SimpleSchubertFlags

/-!
# `X_{sᵢ} = Pᵢ / B ≅ ℙ¹`

Over every commutative ring `R`, for a simple reflection `sᵢ` (`i + 1 < n`):

* `FlagVarieties.lineToSimpleSchubert R n i hi : ℙ¹ ⟶ X_{sᵢ}`, glued from the sections
  `t ↦ (1 + t E_{i+1,i}) B` and `s ↦ (1 + s E_{i,i+1}) sᵢ B` over the two standard charts;
* **`FlagVarieties.simpleSchubertIsoLine R n i hi : X_{sᵢ} ≅ ℙ¹`**, `gB ↦ [g_{ii} : g_{i+1,i}]`,
  with inverse `lineToSimpleSchubert`.
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Foundations.ProjectiveLine ProjectiveLineCharts
open HomogeneousLocalization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra awayAlgebra

variable (R : Type u) [CommRing R] (n : ℕ) (i : ℕ) (hi : i + 1 < n)

/-! ### The chart cover of `ℙ¹` -/

/-- The two standard charts, as an open cover of `ℙ¹`. -/
def chartCover : (scheme R).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin 2) (fun k => Spec (CommRingCat.of (ChartRing R k))) (chartι R)
    (fun x => by
      have hx : x ∈ ⨆ k : Fin 2, chart R k := by rw [iSup_chart_eq_top]; trivial
      obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      rw [← opensRange_chartι] at hk
      obtain ⟨y, hy⟩ := hk
      exact ⟨k, y, hy⟩)

/-! ### The sections over the charts -/

/-- The section of `X_{sᵢ} ⟶ ℙ¹` over the chart `k`. -/
def lineChartSection (k : Fin 2) :
    Spec (CommRingCat.of (ChartRing R k)) ⟶ (simpleSchubert R n i hi).subscheme :=
  Fin.cases (motive := fun k => Spec (CommRingCat.of (ChartRing R k)) ⟶ _)
    (lineChartSection₀ R n i hi)
    (fun j => Fin.cases (motive := fun j : Fin 1 => Spec (CommRingCat.of (ChartRing R j.succ)) ⟶ _)
      (lineChartSection₁ R n i hi) (fun j => j.elim0) j) k

theorem lineChartSection_toLine (k : Fin 2) :
    lineChartSection R n i hi k ≫ simpleSchubertToLine R n i hi = chartι R k := by
  fin_cases k
  · exact lineChartSection₀_toLine R n i hi
  · exact lineChartSection₁_toLine R n i hi

/-! ### The overlap of the charts -/

/-- `X₀ X₁`. -/
abbrev overlapPoly : MvPolynomial (Fin 2) R :=
  MvPolynomial.X 0 * MvPolynomial.X 1

/-- `R[X₀, X₁]_{(X₀)} → R[X₀, X₁]_{(X₀ X₁)}`. -/
def overlapMap₀ : ChartRing R 0 →ₐ[R] Away (grading R) (overlapPoly R) :=
  { awayMap (grading R) (X_mem R 1) (rfl : overlapPoly R = _) with
    commutes' := fun _ => awayMap_fromZeroRingHom (grading R) _ _ _ }

/-- `R[X₀, X₁]_{(X₁)} → R[X₀, X₁]_{(X₀ X₁)}`. -/
def overlapMap₁ : ChartRing R 1 →ₐ[R] Away (grading R) (overlapPoly R) :=
  { awayMap (grading R) (X_mem R 0) (mul_comm _ _ : overlapPoly R = _) with
    commutes' := fun _ => awayMap_fromZeroRingHom (grading R) _ _ _ }

theorem overlapMap_mul :
    overlapMap₀ R (chartFrac R 0 1) * overlapMap₁ R (chartFrac R 1 0) = 1 := by
  apply val_injective
  change (awayMap (grading R) (X_mem R 1) (rfl : overlapPoly R = _) (chartFrac R 0 1) *
    awayMap (grading R) (X_mem R 0) (mul_comm _ _ : overlapPoly R = _) (chartFrac R 1 0)).val = _
  rw [chartFrac, chartFrac, awayMap_mk, awayMap_mk, val_mul, Away.val_mk, Away.val_mk, val_one,
    Localization.mk_mul, Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul, one_mul]
  congr 1
  simp only [Submonoid.coe_mul, pow_one]
  ring

theorem map_transvection {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (a b : Fin n)
    (x : A) : (Matrix.transvection a b x).map φ = Matrix.transvection a b (φ x) := by
  ext r c
  simp only [Matrix.map_apply, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  split_ifs <;> simp

theorem lineChartSection_overlap :
    pullback.fst (chartι R 0) (chartι R 1) ≫ lineChartSection₀ R n i hi =
      pullback.snd (chartι R 0) (chartι R 1) ≫ lineChartSection₁ R n i hi := by
  let e : pullback (chartι R 0) (chartι R 1) ≅
      Spec (CommRingCat.of (Away (grading R) (overlapPoly R))) :=
    Proj.pullbackAwayιIso (grading R) (X_mem R 0) Nat.one_pos (X_mem R 1) Nat.one_pos
      (rfl : overlapPoly R = _)
  have h1 : e.inv ≫ pullback.fst (chartι R 0) (chartι R 1) =
      Spec.map (CommRingCat.ofHom (overlapMap₀ R).toRingHom) :=
    Proj.pullbackAwayιIso_inv_fst _ _ _ _ _ _
  have h2 : e.inv ≫ pullback.snd (chartι R 0) (chartι R 1) =
      Spec.map (CommRingCat.ofHom (overlapMap₁ R).toRingHom) :=
    Proj.pullbackAwayιIso_inv_snd _ _ _ _ _ _
  rw [← cancel_epi e.inv, ← Category.assoc, h1, ← Category.assoc, h2, lineChartSection₀,
    lineChartSection₁, ← Category.assoc, ← Category.assoc, spec_map_parabolicSection,
    spec_map_parabolicSection]
  have hg : (lineChartMatrix₀ R n i hi).map (overlapMap₀ R) = Matrix.transvection (rowB n i hi)
      (rowA n i hi) (overlapMap₀ R (chartFrac R 0 1)) :=
    map_transvection n (overlapMap₀ R).toRingHom _ _ _
  apply parabolicSection_proj_eq
  rw [hg]
  apply blockTriangular_transvection_inv_mul
  · intro r c h
    simp [Matrix.map_apply, lineChartMatrix₁_blockTriangular R n i hi h]
  · rw [Matrix.map_apply, Matrix.map_apply, lineChartMatrix₁_apply_A, lineChartMatrix₁_apply_B,
      chartFrac_self, map_one]
    exact overlapMap_mul R

/-! ### The morphism `ℙ¹ ⟶ X_{sᵢ}` -/

theorem lineChartSection_overlap' :
    pullback.fst (chartι R 1) (chartι R 0) ≫ lineChartSection₁ R n i hi =
      pullback.snd (chartι R 1) (chartι R 0) ≫ lineChartSection₀ R n i hi := by
  have h := lineChartSection_overlap R n i hi
  rw [← pullbackSymmetry_hom_comp_fst, ← pullbackSymmetry_hom_comp_snd, Category.assoc,
    Category.assoc]
  exact (congrArg (fun f => (pullbackSymmetry (chartι R 1) (chartι R 0)).hom ≫ f) h).symm

theorem lineChartSection_compat (x y : Fin 2) :
    pullback.fst ((chartCover R).f x) ((chartCover R).f y) ≫ lineChartSection R n i hi x =
      pullback.snd ((chartCover R).f x) ((chartCover R).f y) ≫ lineChartSection R n i hi y := by
  change pullback.fst (chartι R x) (chartι R y) ≫ _ = pullback.snd (chartι R x) (chartι R y) ≫ _
  by_cases hxy : x = y
  · subst hxy
    rw [(cancel_mono (chartι R x)).1 pullback.condition]
  · fin_cases x <;> fin_cases y
    · exact absurd rfl hxy
    · exact lineChartSection_overlap R n i hi
    · exact lineChartSection_overlap' R n i hi
    · exact absurd rfl hxy

/-- **The morphism `ℙ¹ ⟶ X_{sᵢ}`**, glued from the sections over the two standard charts. -/
def lineToSimpleSchubert : scheme R ⟶ (simpleSchubert R n i hi).subscheme :=
  (chartCover R).glueMorphisms (lineChartSection R n i hi) (lineChartSection_compat R n i hi)

theorem chartι_lineToSimpleSchubert (k : Fin 2) :
    chartι R k ≫ lineToSimpleSchubert R n i hi = lineChartSection R n i hi k :=
  Scheme.Cover.ι_glueMorphisms (chartCover R) _ _ k

theorem lineToSimpleSchubert_toLine :
    lineToSimpleSchubert R n i hi ≫ simpleSchubertToLine R n i hi = 𝟙 _ := by
  refine (chartCover R).hom_ext _ _ fun (k : Fin 2) => ?_
  change chartι R k ≫ _ = chartι R k ≫ _
  rw [← Category.assoc, chartι_lineToSimpleSchubert, lineChartSection_toLine, Category.comp_id]

/-! ### `X_{sᵢ} ⟶ ℙ¹ ⟶ X_{sᵢ}` is the identity -/

section General

variable {X : Scheme.{u}}

theorem eq_toSpecΓ_comp {A : CommRingCat.{u}} (g : X ⟶ Spec A) :
    g = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso A).inv ≫ g.appTop) := by
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem basicOpen_ι_toSpecΓ (r : Γ(X, ⊤)) :
    (X.basicOpen r).ι ≫ X.toSpecΓ =
      Foundations.ProjectiveChartCompatibility.globalBasicOpenMap X r ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Localization.Away r))) := by
  simp only [Foundations.ProjectiveChartCompatibility.globalBasicOpenMap, Category.assoc,
    basicOpenIsoSpecAway_hom_SpecMap]
  erw [Scheme.Hom.resLE_comp_ι]

end General

/-- The evaluation `R[X₀, X₁] → Γ(Pᵢ)`, `(X₀, X₁) ↦ (pᵢᵢ, p_{i+1,i})`. -/
abbrev lineEval : MvPolynomial (Fin 2) R →+* Γ(preimageScheme R n (simpleSchubert R n i hi), ⊤) :=
  evaluation (lineStructure R n i hi) (lineCoordA R n i hi) (lineCoordB R n i hi)

/-- The localization of `Γ(Pᵢ)` on which the chart `k` of `ℙ¹` is read. -/
abbrev lineLoc (k : Fin 2) : Type u :=
  Localization.Away (lineEval R n i hi (MvPolynomial.X k))

instance lineLocAlgebra (k : Fin 2) : Algebra R (lineLoc R n i hi k) :=
  ((algebraMap Γ(preimageScheme R n (simpleSchubert R n i hi), ⊤) (lineLoc R n i hi k)).comp
    (lineStructure R n i hi)).toAlgebra

/-- The generic point of `Pᵢ`, over `lineLoc`. -/
def lineLocPoint (k : Fin 2) : GLCoord R n →ₐ[R] lineLoc R n i hi k :=
  { (algebraMap Γ(preimageScheme R n (simpleSchubert R n i hi), ⊤) (lineLoc R n i hi k)).comp
      (preimageRestrictSections R n _) with
    commutes' := fun _ => rfl }

/-- The chart map of `ℙ¹` read on `Pᵢ`. -/
def lineLocMap (k : Fin 2) : ChartRing R k →ₐ[R] lineLoc R n i hi k :=
  { Foundations.ProjectiveChartCompatibility.evaluatedAwayMap (grading R) (lineEval R n i hi)
      (MvPolynomial.X k) with
    commutes' := fun r => by
      change Localization.awayMap (lineEval R n i hi) _
        (algebraMap _ _ (chartStructure R k r)) = _
      rw [HomogeneousLocalization.algebraMap_apply, val_chartStructure, Localization.awayMap,
        IsLocalization.Away.map, IsLocalization.map_eq, evaluation_C]
      rfl }

theorem lineLocMap_chartFrac (k j : Fin 2) :
    lineLocMap R n i hi k (chartFrac R k j) *
        algebraMap _ (lineLoc R n i hi k) (lineEval R n i hi (MvPolynomial.X k)) =
      algebraMap _ (lineLoc R n i hi k) (lineEval R n i hi (MvPolynomial.X j)) := by
  change Localization.awayMap (lineEval R n i hi) _ (algebraMap _ _ (chartFrac R k j)) * _ = _
  rw [HomogeneousLocalization.algebraMap_apply, chartFrac, Away.val_mk, Localization.mk_eq_mk',
    Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_mk']
  have key : ∀ y : Submonoid.powers (lineEval R n i hi (MvPolynomial.X k)),
      (y : Γ(preimageScheme R n (simpleSchubert R n i hi), ⊤)) =
        lineEval R n i hi (MvPolynomial.X k) →
      IsLocalization.mk' (lineLoc R n i hi k) (lineEval R n i hi (MvPolynomial.X j)) y *
          algebraMap _ (lineLoc R n i hi k) (lineEval R n i hi (MvPolynomial.X k)) =
        algebraMap _ (lineLoc R n i hi k) (lineEval R n i hi (MvPolynomial.X j)) := by
    rintro y hy
    have h := IsLocalization.mk'_spec (lineLoc R n i hi k) (lineEval R n i hi (MvPolynomial.X j)) y
    rw [hy] at h
    exact h
  exact key _ (by simp)

theorem lineLocPoint_genericMatrix (k : Fin 2) (r c : Fin n) :
    lineLocPoint R n i hi k (genericMatrix R n r c) =
      algebraMap Γ(preimageScheme R n (simpleSchubert R n i hi), ⊤) (lineLoc R n i hi k)
        (preimageRestrictSections R n _ (genericMatrix R n r c)) :=
  rfl

theorem lineLocPoint_blockTriangular (k : Fin 2) :
    ((genericMatrix R n).map (lineLocPoint R n i hi k)).BlockTriangular (parabolicBlock n i) := by
  intro r c h
  rw [Matrix.map_apply, lineLocPoint_genericMatrix]
  have hmem := genericMatrix_mem_preimageIdeal R n i hi r c h
  rw [← ker_preimageRestrictSections, RingHom.mem_ker] at hmem
  rw [hmem, map_zero]

theorem basicOpen_ι_parabolicToLine (k : Fin 2) :
    ((preimageScheme R n (simpleSchubert R n i hi)).basicOpen
        (lineEval R n i hi (MvPolynomial.X k))).ι ≫ parabolicToLine R n i hi =
      Foundations.ProjectiveChartCompatibility.globalBasicOpenMap _
          (lineEval R n i hi (MvPolynomial.X k)) ≫
        Spec.map (CommRingCat.ofHom (lineLocMap R n i hi k).toRingHom) ≫ chartι R k := by
  rw [parabolicToLine, fromPair, ← Scheme.Hom.resLE_comp_ι _
    (Proj.fromOfGlobalSections_preimage_basicOpen (grading R) _ _ Nat.one_pos (X_mem R k)).ge,
    Proj.fromOfGlobalSections_resLE (grading R) _ _ Nat.one_pos (X_mem R k),
    Foundations.ProjectiveChartCompatibility.toBasicOpen_ι_eq (grading R) _ (X_mem R k)
      Nat.one_pos]
  rfl

theorem basicOpen_ι_preimageι (k : Fin 2) :
    ((preimageScheme R n (simpleSchubert R n i hi)).basicOpen
        (lineEval R n i hi (MvPolynomial.X k))).ι ≫ preimageι R n _ =
      Foundations.ProjectiveChartCompatibility.globalBasicOpenMap _
          (lineEval R n i hi (MvPolynomial.X k)) ≫
        GLScheme.point R n (lineLocPoint R n i hi k) := by
  rw [← cancel_mono (TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom, Category.assoc,
    Category.assoc, show GLScheme.point R n (lineLocPoint R n i hi k) =
      Spec.map (CommRingCat.ofHom (lineLocPoint R n i hi k).toRingHom) ≫
        (TauCeti.GeneralLinear.groupSchemeSpecIso R n).inv from rfl, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  conv_lhs => rw [eq_toSpecΓ_comp
    (preimageι R n _ ≫ (TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom)]
  rw [← Category.assoc, basicOpen_ι_toSpecΓ, Category.assoc, ← Spec.map_comp]
  congr 1

theorem preimageProj_eq_of_orbitMap_eq {T : Scheme.{u}}
    (a b : T ⟶ preimageScheme R n (simpleSchubert R n i hi))
    (h : a ≫ preimageι R n _ ≫ FlagScheme.orbitMap R n =
      b ≫ preimageι R n _ ≫ FlagScheme.orbitMap R n) :
    a ≫ preimageProj R n _ = b ≫ preimageProj R n _ := by
  rw [← cancel_mono (simpleSchubert R n i hi).subschemeι, Category.assoc, Category.assoc,
    ← pullback.condition]
  exact h

theorem basicOpen_ι_lineToSimpleSchubert (k : Fin 2)
    (g : Matrix (Fin n) (Fin n) (ChartRing R k)) (hg : IsUnit g.det)
    (hb : g.BlockTriangular (parabolicBlock n i))
    (hσ : lineChartSection R n i hi k =
      parabolicSection (R := R) (hi := hi) g hg hb ≫ preimageProj R n _)
    (hflag : ((g.map (lineLocMap R n i hi k))⁻¹ *
      (genericMatrix R n).map (lineLocPoint R n i hi k)).BlockTriangular id) :
    ((preimageScheme R n (simpleSchubert R n i hi)).basicOpen
        (lineEval R n i hi (MvPolynomial.X k))).ι ≫
        parabolicToLine R n i hi ≫ lineToSimpleSchubert R n i hi =
      ((preimageScheme R n (simpleSchubert R n i hi)).basicOpen
        (lineEval R n i hi (MvPolynomial.X k))).ι ≫ preimageProj R n _ := by
  rw [← Category.assoc, basicOpen_ι_parabolicToLine, Category.assoc, Category.assoc,
    chartι_lineToSimpleSchubert, hσ, ← Category.assoc (Spec.map _), ← Category.assoc]
  apply preimageProj_eq_of_orbitMap_eq
  simp only [Category.assoc]
  rw [parabolicSection_ι_assoc, ← Category.assoc (Spec.map _), spec_map_comp_point,
    ← Category.assoc (Scheme.Opens.ι _), basicOpen_ι_preimageι, Category.assoc]
  congr 1
  apply orbitMap_point_eq_of_blockTriangular
  rw [pointMatrix_comp, pointMatrix_glPointOfMatrix]
  exact hflag

theorem lineEval_X_zero :
    lineEval R n i hi (MvPolynomial.X 0) =
      preimageRestrictSections R n _ (genericMatrix R n (rowA n i hi) (rowA n i hi)) :=
  evaluation_X _ _ _ 0

theorem lineEval_X_one :
    lineEval R n i hi (MvPolynomial.X 1) =
      preimageRestrictSections R n _ (genericMatrix R n (rowB n i hi) (rowA n i hi)) :=
  evaluation_X _ _ _ 1

theorem basicOpen_ι_lineToSimpleSchubert₀ :
    ((preimageScheme R n (simpleSchubert R n i hi)).basicOpen
        (lineEval R n i hi (MvPolynomial.X 0))).ι ≫
        parabolicToLine R n i hi ≫ lineToSimpleSchubert R n i hi =
      ((preimageScheme R n (simpleSchubert R n i hi)).basicOpen
        (lineEval R n i hi (MvPolynomial.X 0))).ι ≫ preimageProj R n _ := by
  refine basicOpen_ι_lineToSimpleSchubert R n i hi 0 (lineChartMatrix₀ R n i hi)
    (isUnit_det_lineChartMatrix₀ R n i hi) (lineChartMatrix₀_blockTriangular R n i hi) rfl ?_
  rw [lineChartMatrix₀, show (Matrix.transvection (rowB n i hi) (rowA n i hi)
      (chartFrac R 0 1)).map (lineLocMap R n i hi 0) = Matrix.transvection (rowB n i hi)
      (rowA n i hi) (lineLocMap R n i hi 0 (chartFrac R 0 1)) from
    map_transvection n (lineLocMap R n i hi 0).toRingHom _ _ _]
  apply blockTriangular_transvection_inv_mul i hi _ (lineLocPoint_blockTriangular R n i hi 0)
  rw [Matrix.map_apply, Matrix.map_apply, lineLocPoint_genericMatrix,
    lineLocPoint_genericMatrix, ← lineEval_X_zero, ← lineEval_X_one]
  exact lineLocMap_chartFrac R n i hi 0 1

theorem basicOpen_ι_lineToSimpleSchubert₁ :
    ((preimageScheme R n (simpleSchubert R n i hi)).basicOpen
        (lineEval R n i hi (MvPolynomial.X 1))).ι ≫
        parabolicToLine R n i hi ≫ lineToSimpleSchubert R n i hi =
      ((preimageScheme R n (simpleSchubert R n i hi)).basicOpen
        (lineEval R n i hi (MvPolynomial.X 1))).ι ≫ preimageProj R n _ := by
  refine basicOpen_ι_lineToSimpleSchubert R n i hi 1 (lineChartMatrix₁ R n i hi)
    (isUnit_det_lineChartMatrix₁ R n i hi) (lineChartMatrix₁_blockTriangular R n i hi) rfl ?_
  rw [lineChartMatrix₁, Matrix.map_mul, show (Matrix.transvection (rowA n i hi) (rowB n i hi)
      (chartFrac R 1 0)).map (lineLocMap R n i hi 1) = Matrix.transvection (rowA n i hi)
      (rowB n i hi) (lineLocMap R n i hi 1 (chartFrac R 1 0)) from
    map_transvection n (lineLocMap R n i hi 1).toRingHom _ _ _,
    show (permMatrix n (simpleReflection n i hi)).map (lineLocMap R n i hi 1) =
      permMatrix n (simpleReflection n i hi) from
      permMatrix_map (v := simpleReflection n i hi) (lineLocMap R n i hi 1)]
  apply blockTriangular_transvection_perm_inv_mul i hi _ (lineLocPoint_blockTriangular R n i hi 1)
  rw [Matrix.map_apply, Matrix.map_apply, lineLocPoint_genericMatrix,
    lineLocPoint_genericMatrix, ← lineEval_X_zero, ← lineEval_X_one]
  exact lineLocMap_chartFrac R n i hi 1 0

theorem parabolicToLine_lineToSimpleSchubert :
    parabolicToLine R n i hi ≫ lineToSimpleSchubert R n i hi = preimageProj R n _ := by
  refine Scheme.hom_ext_of_forall _ _ fun p => ?_
  have hp : parabolicToLine R n i hi p ∈ ⨆ k : Fin 2, chart R k := by
    rw [iSup_chart_eq_top]
    trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
  refine ⟨(preimageScheme R n (simpleSchubert R n i hi)).basicOpen
    (lineEval R n i hi (MvPolynomial.X k)), ?_, ?_⟩
  · rw [← Proj.fromOfGlobalSections_preimage_basicOpen (grading R) _ _ Nat.one_pos (X_mem R k)]
    exact hk
  · fin_cases k
    · exact basicOpen_ι_lineToSimpleSchubert₀ R n i hi
    · exact basicOpen_ι_lineToSimpleSchubert₁ R n i hi

theorem simpleSchubertToLine_lineToSimpleSchubert :
    simpleSchubertToLine R n i hi ≫ lineToSimpleSchubert R n i hi = 𝟙 _ := by
  apply preimageDesc_ext
  rw [preimageProj_simpleSchubertToLine_assoc, Category.comp_id]
  exact parabolicToLine_lineToSimpleSchubert R n i hi

/-- **`X_{sᵢ} = Pᵢ / B ≅ ℙ¹`** (over every commutative ring), `gB ↦ [g_{ii} : g_{i+1,i}]`. -/
def simpleSchubertIsoLine : (simpleSchubert R n i hi).subscheme ≅ scheme R where
  hom := simpleSchubertToLine R n i hi
  inv := lineToSimpleSchubert R n i hi
  hom_inv_id := simpleSchubertToLine_lineToSimpleSchubert R n i hi
  inv_hom_id := lineToSimpleSchubert_toLine R n i hi

end FlagVarieties
