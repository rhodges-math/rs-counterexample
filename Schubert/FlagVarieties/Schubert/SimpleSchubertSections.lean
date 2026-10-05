import Schubert.FlagVarieties.Schubert.SimpleSchubert

/-!
# Sections of `X_{sᵢ} ⟶ ℙ¹` over the charts

* `FlagVarieties.parabolicSection g`: for a matrix `g ∈ Pᵢ(A)`, the `A`-point of `π⁻¹(X_{sᵢ}) = Pᵢ`;
  it maps to `[g_{ii} : g_{i+1,i}]` in `ℙ¹` (`parabolicSection_parabolicToLine`);
* `FlagVarieties.lineChartSection₀`, `lineChartSection₁`: the points `1 + t E_{i+1,i}` and
  `(1 + s E_{i,i+1}) sᵢ` over the two standard charts of `ℙ¹`, which map to the chart inclusions
  (`lineChartSection₀_toLine`, `lineChartSection₁_toLine`).
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Foundations.ProjectiveLine ProjectiveLineCharts
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ) (i : ℕ) (hi : i + 1 < n)

/-! ### Points of `Pᵢ` -/

section Points

variable {R n i hi} {A : Type u} [CommRing A] [Algebra R A] (g : Matrix (Fin n) (Fin n) A)
  (hg : IsUnit g.det) (hb : g.BlockTriangular (parabolicBlock n i))

include hb in
theorem preimageIdeal_le_ker_glPointOfMatrix :
    preimageIdeal R n (simpleSchubert R n i hi) ≤
      RingHom.ker (glPointOfMatrix R g hg).toRingHom := by
  rw [preimageIdeal_simpleSchubert]
  intro f hf
  rw [RingHom.mem_ker]
  have h : glPointOfMatrix R g hg =
      (parabolicPointOfMatrix i g hg hb).comp (Ideal.Quotient.mkₐ R (parabolicIdeal R n i)) :=
    rfl
  change glPointOfMatrix R g hg f = 0
  rw [h, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hf,
    map_zero]

/-- The ring map `𝒪(Pᵢ) → A` of a point `g ∈ Pᵢ(A)`. -/
def parabolicPointRing : GLCoord R n ⧸ preimageIdeal R n (simpleSchubert R n i hi) →+* A :=
  Ideal.Quotient.lift _ (glPointOfMatrix R g hg).toRingHom
    (fun _ hf => (preimageIdeal_le_ker_glPointOfMatrix (hi := hi) g hg hb) hf)

/-- **The `A`-point `g` of `π⁻¹(X_{sᵢ}) = Pᵢ`.** -/
def parabolicSection :
    Spec (CommRingCat.of A) ⟶ preimageScheme R n (simpleSchubert R n i hi) :=
  Spec.map (CommRingCat.ofHom (parabolicPointRing (hi := hi) g hg hb)) ≫
    preimageSpecMap R n _

@[reassoc] theorem parabolicSection_ι :
    parabolicSection (hi := hi) g hg hb ≫ preimageι R n _ =
      GLScheme.point R n (glPointOfMatrix R g hg) := by
  rw [parabolicSection, Category.assoc, preimageSpecMap_ι, GLScheme.point]
  change Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map _ ≫ _
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

theorem parabolicSection_appTop (f : GLCoord R n) :
    (parabolicSection (hi := hi) g hg hb).appTop (preimageRestrictSections R n _ f) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv (glPointOfMatrix R g hg f) := by
  rw [← point_appTop_glCoordToGlobal, ← parabolicSection_ι (hi := hi) g hg hb,
    Scheme.Hom.comp_appTop]
  rfl

omit hb in
theorem glPointOfMatrix_genericMatrix' (r c : Fin n) :
    glPointOfMatrix R g hg (genericMatrix R n r c) = g r c := by
  have h := congrFun (congrFun (genericMatrix_map_glPointOfMatrix R g hg) r) c
  rwa [Matrix.map_apply] at h

/-- **The point `g ∈ Pᵢ(A)` maps to `[g_{ii} : g_{i+1,i}]` in `ℙ¹`.** -/
theorem parabolicSection_parabolicToLine :
    parabolicSection (hi := hi) g hg hb ≫ parabolicToLine R n i hi =
      fromPair ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.comp (algebraMap R A))
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (g (rowA n i hi) (rowA n i hi)))
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (g (rowB n i hi) (rowA n i hi)))
        (by
          have h := (isCoprime_lineCoord R n i hi).map
            (parabolicSection (hi := hi) g hg hb).appTop.hom
          rwa [parabolicSection_appTop, parabolicSection_appTop,
            glPointOfMatrix_genericMatrix', glPointOfMatrix_genericMatrix'] at h) := by
  rw [parabolicToLine, fromPair_naturality]
  apply fromPair_congr
  · ext r
    simp only [RingHom.comp_apply]
    rw [parabolicSection_appTop, AlgHom.commutes]
  · rw [parabolicSection_appTop, glPointOfMatrix_genericMatrix']
  · rw [parabolicSection_appTop, glPointOfMatrix_genericMatrix']

end Points

/-! ### The sections over the charts of `ℙ¹` -/

/-- The `R`-algebra structure of `R[X₀, X₁]_{(f)}`. -/
abbrev awayAlgebra (f : MvPolynomial (Fin 2) R) :
    Algebra R (HomogeneousLocalization.Away (grading R) f) :=
  ((HomogeneousLocalization.fromZeroRingHom (grading R) _).comp (constants R)).toAlgebra

attribute [local instance] awayAlgebra

theorem algebraMap_chartRing (k : Fin 2) : algebraMap R (ChartRing R k) = chartStructure R k :=
  rfl

theorem rowA_ne_rowB : rowA n i hi ≠ rowB n i hi := by
  simp [Fin.ext_iff]

theorem rowA_lt_rowB : rowA n i hi < rowB n i hi := by
  simp [Fin.lt_def]

/-- The point `1 + t E_{i+1,i}` of `Pᵢ` over the chart `X₀ ≠ 0`, `t = X₁ / X₀`. -/
def lineChartMatrix₀ : Matrix (Fin n) (Fin n) (ChartRing R 0) :=
  Matrix.transvection (rowB n i hi) (rowA n i hi) (chartFrac R 0 1)

/-- The point `(1 + s E_{i,i+1}) sᵢ` of `Pᵢ` over the chart `X₁ ≠ 0`, `s = X₀ / X₁`. -/
def lineChartMatrix₁ : Matrix (Fin n) (Fin n) (ChartRing R 1) :=
  Matrix.transvection (rowA n i hi) (rowB n i hi) (chartFrac R 1 0) *
    permMatrix n (simpleReflection n i hi)

theorem isUnit_det_lineChartMatrix₀ : IsUnit (lineChartMatrix₀ R n i hi).det := by
  rw [lineChartMatrix₀, Matrix.det_transvection_of_ne _ _ (rowA_ne_rowB n i hi).symm]
  exact isUnit_one

theorem isUnit_det_lineChartMatrix₁ : IsUnit (lineChartMatrix₁ R n i hi).det := by
  rw [lineChartMatrix₁, Matrix.det_mul, Matrix.det_transvection_of_ne _ _ (rowA_ne_rowB n i hi),
    one_mul]
  exact isUnit_det_permMatrix n _

theorem lineChartMatrix₀_blockTriangular :
    (lineChartMatrix₀ R n i hi).BlockTriangular (parabolicBlock n i) := by
  intro r c h
  rw [parabolicBlock_lt_iff] at h
  have hrc : r ≠ c := fun e => by rw [e] at h; exact lt_irrefl _ h.1
  simp only [lineChartMatrix₀, Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne hrc,
    zero_add, Matrix.single_apply]
  split_ifs with h'
  · obtain ⟨rfl, rfl⟩ := h'
    exact absurd ⟨rfl, rfl⟩ h.2
  · rfl

theorem lineChartMatrix₁_blockTriangular :
    (lineChartMatrix₁ R n i hi).BlockTriangular (parabolicBlock n i) :=
  Matrix.BlockTriangular.mul (blockTriangular_parabolicBlock_of_upper i
    (transvection_blockTriangular (rowA_lt_rowB n i hi) _))
    (blockTriangular_permMatrix_simpleReflection i hi)

theorem lineChartMatrix₀_apply_A :
    lineChartMatrix₀ R n i hi (rowA n i hi) (rowA n i hi) = chartFrac R 0 0 := by
  rw [chartFrac_self]
  simp [lineChartMatrix₀, Matrix.transvection]

theorem lineChartMatrix₀_apply_B :
    lineChartMatrix₀ R n i hi (rowB n i hi) (rowA n i hi) = chartFrac R 0 1 := by
  simp [lineChartMatrix₀, Matrix.transvection, (rowA_ne_rowB n i hi).symm]

theorem lineChartMatrix₁_apply_A :
    lineChartMatrix₁ R n i hi (rowA n i hi) (rowA n i hi) = chartFrac R 1 0 := by
  rw [lineChartMatrix₁, mul_permMatrix_apply, simpleReflection, Equiv.swap_apply_left]
  simp [Matrix.transvection, rowA_ne_rowB n i hi]

theorem lineChartMatrix₁_apply_B :
    lineChartMatrix₁ R n i hi (rowB n i hi) (rowA n i hi) = chartFrac R 1 1 := by
  rw [chartFrac_self, lineChartMatrix₁, mul_permMatrix_apply, simpleReflection,
    Equiv.swap_apply_left]
  simp [Matrix.transvection]

/-- The section of `X_{sᵢ} ⟶ ℙ¹` over the chart `X₀ ≠ 0`. -/
def lineChartSection₀ :
    Spec (CommRingCat.of (ChartRing R 0)) ⟶ (simpleSchubert R n i hi).subscheme :=
  parabolicSection (hi := hi) (lineChartMatrix₀ R n i hi) (isUnit_det_lineChartMatrix₀ R n i hi)
    (lineChartMatrix₀_blockTriangular R n i hi) ≫ preimageProj R n _

/-- The section of `X_{sᵢ} ⟶ ℙ¹` over the chart `X₁ ≠ 0`. -/
def lineChartSection₁ :
    Spec (CommRingCat.of (ChartRing R 1)) ⟶ (simpleSchubert R n i hi).subscheme :=
  parabolicSection (hi := hi) (lineChartMatrix₁ R n i hi) (isUnit_det_lineChartMatrix₁ R n i hi)
    (lineChartMatrix₁_blockTriangular R n i hi) ≫ preimageProj R n _

theorem lineChartSection₀_toLine :
    lineChartSection₀ R n i hi ≫ simpleSchubertToLine R n i hi = chartι R 0 := by
  rw [lineChartSection₀, Category.assoc, preimageProj_simpleSchubertToLine,
    parabolicSection_parabolicToLine, chartι_eq_fromPair]
  apply fromPair_congr
  · rfl
  · rw [lineChartMatrix₀_apply_A]
  · rw [lineChartMatrix₀_apply_B]

theorem lineChartSection₁_toLine :
    lineChartSection₁ R n i hi ≫ simpleSchubertToLine R n i hi = chartι R 1 := by
  rw [lineChartSection₁, Category.assoc, preimageProj_simpleSchubertToLine,
    parabolicSection_parabolicToLine, chartι_eq_fromPair]
  apply fromPair_congr
  · rfl
  · rw [lineChartMatrix₁_apply_A]
  · rw [lineChartMatrix₁_apply_B]

end FlagVarieties
