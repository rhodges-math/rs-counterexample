import RSCounterexample.FlagVarieties.Foundations.Schemes.GeneralLinearGrassmannianLawsUnit

/-! The unit section and its scheme-level action law. -/

noncomputable section
set_option linter.style.haveILetI false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : Type u) [CommRing R] (n d : ℕ)

/-- The section `Q ↦ (1, Q)` of the projection `GLₙ ×_R Gr ⟶ Gr`. -/
def generalLinearGrassmannianUnitSection :
    selectedChartScheme R n d ⟶ generalLinearGrassmannianProduct R n d :=
  pullback.lift
    (selectedChartSchemeToSpec R n d ≫
      generalLinearGroupPoint R R n (generalLinearUnitAlgebraPoint R R n))
    (𝟙 (selectedChartScheme R n d)) (by
      have hu : generalLinearGroupPoint R R n (generalLinearUnitAlgebraPoint R R n) ≫
          (TauCeti.GeneralLinear.groupScheme R n).X.hom = 𝟙 _ := by
        rw [generalLinearGroupPoint_toSpec]
        simp
      rw [Category.assoc, hu]
      simp)

@[reassoc] theorem generalLinearGrassmannianUnitSection_group :
    generalLinearGrassmannianUnitSection R n d ≫
      generalLinearGrassmannianGroup R n d =
    selectedChartSchemeToSpec R n d ≫
      generalLinearGroupPoint R R n (generalLinearUnitAlgebraPoint R R n) := by
  exact pullback.lift_fst _ _ _

@[reassoc] theorem generalLinearGrassmannianUnitSection_point :
    generalLinearGrassmannianUnitSection R n d ≫
      generalLinearGrassmannianPoint R n d = 𝟙 _ := by
  exact pullback.lift_snd _ _ _

private theorem generalLinearGroupPoint_unit_baseChange
    (B : Type u) [CommRing B] [Algebra R B] :
    Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫
      generalLinearGroupPoint R R n (generalLinearUnitAlgebraPoint R R n) =
    generalLinearGroupPoint R B n (generalLinearUnitAlgebraPoint R B n) := by
  apply (cancel_mono (TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom).mp
  unfold generalLinearGroupPoint
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Spec.map_comp]
  congr 1

private theorem generalLinearGrassmannianUnitSection_affine
    (B : Type u) [CommRing B] [Algebra R B]
    (P : Module.Grassmannian B (Fin n → B) d) :
    selectedQuotientMorphism R P ≫ generalLinearGrassmannianUnitSection R n d =
      generalLinearGrassmannianOfAffine R B n d
        (generalLinearUnitAlgebraPoint R B n) P := by
  apply pullback.hom_ext
  · change selectedQuotientMorphism R P ≫ generalLinearGrassmannianUnitSection R n d ≫
        generalLinearGrassmannianGroup R n d =
        generalLinearGrassmannianOfAffine R B n d
          (generalLinearUnitAlgebraPoint R B n) P ≫
          generalLinearGrassmannianGroup R n d
    rw [generalLinearGrassmannianUnitSection_group,
      generalLinearGrassmannianOfAffine_group, ← Category.assoc,
      selectedQuotientMorphism_toSpec]
    exact generalLinearGroupPoint_unit_baseChange R n B
  · change selectedQuotientMorphism R P ≫ generalLinearGrassmannianUnitSection R n d ≫
        generalLinearGrassmannianPoint R n d =
        generalLinearGrassmannianOfAffine R B n d
          (generalLinearUnitAlgebraPoint R B n) P ≫
          generalLinearGrassmannianPoint R n d
    rw [generalLinearGrassmannianUnitSection_point,
      Category.comp_id, generalLinearGrassmannianOfAffine_point]

private theorem generalLinearGrassmannianAction_unit_test
    (A : Type u) [CommRing A] [Algebra R A]
    (j : Spec (CommRingCat.of A) ⟶ selectedChartScheme R n d)
    (hF : j ≫ selectedChartSchemeToSpec R n d =
      Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    j ≫ (generalLinearGrassmannianUnitSection R n d ≫
      generalLinearGrassmannianAction R n d) = j := by
  let P := quotientOfSelectedMorphism j hF
  have hj : selectedQuotientMorphism R P = j :=
    selectedQuotientMorphism_quotientOfSelectedMorphism j hF
  calc
    j ≫ (generalLinearGrassmannianUnitSection R n d ≫
        generalLinearGrassmannianAction R n d) =
      (selectedQuotientMorphism R P ≫
        generalLinearGrassmannianUnitSection R n d) ≫
          generalLinearGrassmannianAction R n d := by rw [hj, Category.assoc]
    _ = generalLinearGrassmannianOfAffine R A n d
          (generalLinearUnitAlgebraPoint R A n) P ≫
            generalLinearGrassmannianAction R n d := by
      rw [generalLinearGrassmannianUnitSection_affine]
    _ = selectedQuotientMorphism R P :=
      generalLinearGrassmannianAction_unit_affine R A n d P
    _ = j := hj

/-- The varying general-linear action has the group-unit law as an
equality of scheme morphisms, tested on the canonical affine open cover. -/
theorem generalLinearGrassmannianAction_unit :
    generalLinearGrassmannianUnitSection R n d ≫
      generalLinearGrassmannianAction R n d =
    𝟙 (selectedChartScheme R n d) := by
  let C := (selectedChartScheme R n d).affineOpenCover
  apply C.openCover.hom_ext
  intro i
  let j := C.f i
  let A := C.X i
  let b : Spec A ⟶ Spec (CommRingCat.of R) :=
    j ≫ selectedChartSchemeToSpec R n d
  letI : Algebra R A := (Spec.fullyFaithful.preimage b).unop.hom.toAlgebra
  have hb : Spec.map (CommRingCat.ofHom (algebraMap R A)) = b := by
    change Spec.map (Spec.fullyFaithful.preimage b).unop = b
    exact Spec.map_preimage_unop b
  change j ≫ (generalLinearGrassmannianUnitSection R n d ≫
    generalLinearGrassmannianAction R n d) = j ≫ 𝟙 _
  rw [Category.comp_id]
  exact @generalLinearGrassmannianAction_unit_test R _ n d A _
    ((Spec.fullyFaithful.preimage b).unop.hom.toAlgebra) j hb.symm

end FlagVarieties.Foundations.QuotientCharts
