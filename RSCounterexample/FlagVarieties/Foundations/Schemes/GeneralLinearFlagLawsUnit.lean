import RSCounterexample.FlagVarieties.Foundations.Schemes.GeneralLinearFlagEvaluation
import RSCounterexample.FlagVarieties.Foundations.Schemes.GeneralLinearGrassmannianLawsUnit

/-! The group unit fixes the varying flag action. -/

noncomputable section
set_option linter.style.haveILetI false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Matrix
universe u
variable (R : Type u) [CommRing R] (n : ℕ)

theorem generalLinearFlagAction_unit_affine
    (B : Type u) [CommRing B] [Algebra R B]
    (P : RingFlag B (Fin n → B) n) :
    generalLinearFlagOfAffine R B n (generalLinearUnitAlgebraPoint R B n) P ≫
      generalLinearFlagAction R n = simultaneousFlagRelativeMorphism R P := by
  rw [generalLinearFlagAction_evaluate]
  have he : ((generalLinearMatrixAt R B n
      (generalLinearUnitAlgebraPoint R B n)).toLinearEquiv'
        (generalLinearMatrixAt_isUnit R B n
          (generalLinearUnitAlgebraPoint R B n)).invertible) =
      LinearEquiv.refl B (Fin n → B) := by
    apply LinearEquiv.ext
    intro x
    change generalLinearMatrixAt R B n
      (generalLinearUnitAlgebraPoint R B n) *ᵥ x = x
    rw [generalLinearMatrixAt_unit]
    simp
  rw [he, RingFlag.transport_refl]

/-- The section `V• ↦ (1, V•)` of the projection `GLₙ ×_R Flₙ ⟶ Flₙ`. -/
def generalLinearFlagUnitSection :
    selectedFlagChartScheme R n ⟶ generalLinearFlagProduct R n :=
  pullback.lift
    (selectedFlagChartSchemeToSpec R n ≫
      generalLinearGroupPoint R R n (generalLinearUnitAlgebraPoint R R n))
    (𝟙 (selectedFlagChartScheme R n)) (by
      have hu : generalLinearGroupPoint R R n (generalLinearUnitAlgebraPoint R R n) ≫
          (TauCeti.GeneralLinear.groupScheme R n).X.hom = 𝟙 _ := by
        rw [generalLinearGroupPoint_toSpec]
        simp
      rw [Category.assoc, hu]
      simp)

@[reassoc] theorem generalLinearFlagUnitSection_group :
    generalLinearFlagUnitSection R n ≫ generalLinearFlagGroup R n =
    selectedFlagChartSchemeToSpec R n ≫
      generalLinearGroupPoint R R n (generalLinearUnitAlgebraPoint R R n) := by
  exact pullback.lift_fst _ _ _

@[reassoc] theorem generalLinearFlagUnitSection_point :
    generalLinearFlagUnitSection R n ≫ generalLinearFlagPoint R n = 𝟙 _ := by
  exact pullback.lift_snd _ _ _

private theorem generalLinearGroupPoint_unit_baseChange_flag
    (B : Type u) [CommRing B] [Algebra R B] :
    Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫
      generalLinearGroupPoint R R n (generalLinearUnitAlgebraPoint R R n) =
    generalLinearGroupPoint R B n (generalLinearUnitAlgebraPoint R B n) := by
  apply (cancel_mono (TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom).mp
  unfold generalLinearGroupPoint
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Spec.map_comp]
  congr 1

private theorem generalLinearFlagUnitSection_affine
    (B : Type u) [CommRing B] [Algebra R B]
    (P : RingFlag B (Fin n → B) n) :
    simultaneousFlagRelativeMorphism R P ≫ generalLinearFlagUnitSection R n =
      generalLinearFlagOfAffine R B n (generalLinearUnitAlgebraPoint R B n) P := by
  apply pullback.hom_ext
  · change simultaneousFlagRelativeMorphism R P ≫ generalLinearFlagUnitSection R n ≫
        generalLinearFlagGroup R n =
        generalLinearFlagOfAffine R B n
          (generalLinearUnitAlgebraPoint R B n) P ≫ generalLinearFlagGroup R n
    rw [generalLinearFlagUnitSection_group, generalLinearFlagOfAffine_group,
      ← Category.assoc, simultaneousFlagRelativeMorphism_toSpec]
    exact generalLinearGroupPoint_unit_baseChange_flag R n B
  · change simultaneousFlagRelativeMorphism R P ≫ generalLinearFlagUnitSection R n ≫
        generalLinearFlagPoint R n =
        generalLinearFlagOfAffine R B n
          (generalLinearUnitAlgebraPoint R B n) P ≫ generalLinearFlagPoint R n
    rw [generalLinearFlagUnitSection_point, Category.comp_id,
      generalLinearFlagOfAffine_point]

private theorem generalLinearFlagAction_unit_test
    (B : Type u) [CommRing B] [Algebra R B]
    (j : Spec (CommRingCat.of B) ⟶ selectedFlagChartScheme R n)
    (hj : j ≫ selectedFlagChartSchemeToSpec R n =
      Spec.map (CommRingCat.ofHom (algebraMap R B))) :
    j ≫ (generalLinearFlagUnitSection R n ≫ generalLinearFlagAction R n) = j := by
  let P := selectedFlagRingOfAffine R (CommRingCat.of B) n ⟨j, hj⟩
  have hP : simultaneousFlagRelativeMorphism R P = j :=
    congrArg Subtype.val
      (selectedFlagAffineOfRing_ringOfAffine R (CommRingCat.of B) n ⟨j, hj⟩)
  calc
    j ≫ (generalLinearFlagUnitSection R n ≫ generalLinearFlagAction R n) =
      (simultaneousFlagRelativeMorphism R P ≫ generalLinearFlagUnitSection R n) ≫
        generalLinearFlagAction R n := by rw [hP, Category.assoc]
    _ = generalLinearFlagOfAffine R B n (generalLinearUnitAlgebraPoint R B n) P ≫
        generalLinearFlagAction R n := by rw [generalLinearFlagUnitSection_affine]
    _ = simultaneousFlagRelativeMorphism R P := generalLinearFlagAction_unit_affine R n B P
    _ = j := hP

/-- The varying flag action has the group-unit law as an equality
of scheme morphisms. -/
theorem generalLinearFlagAction_unit :
    generalLinearFlagUnitSection R n ≫ generalLinearFlagAction R n =
      𝟙 (selectedFlagChartScheme R n) := by
  let C := (selectedFlagChartScheme R n).affineOpenCover
  apply C.openCover.hom_ext
  intro i
  let j := C.f i
  let B := C.X i
  let b : Spec B ⟶ Spec (CommRingCat.of R) :=
    j ≫ selectedFlagChartSchemeToSpec R n
  letI : Algebra R B := (Spec.fullyFaithful.preimage b).unop.hom.toAlgebra
  have hb : Spec.map (CommRingCat.ofHom (algebraMap R B)) = b := by
    change Spec.map (Spec.fullyFaithful.preimage b).unop = b
    exact Spec.map_preimage_unop b
  change j ≫ (generalLinearFlagUnitSection R n ≫ generalLinearFlagAction R n) = j ≫ 𝟙 _
  rw [Category.comp_id]
  exact @generalLinearFlagAction_unit_test R _ n B _
    ((Spec.fullyFaithful.preimage b).unop.hom.toAlgebra) j hb.symm

end FlagVarieties.Foundations.QuotientCharts
