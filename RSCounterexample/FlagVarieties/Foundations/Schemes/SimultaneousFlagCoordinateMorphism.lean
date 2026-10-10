import RSCounterexample.FlagVarieties.Foundations.Schemes.SimultaneousFlagCoordinateGlue
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedQuotientMorphismNaturality

/-!
# Global flag-scheme morphism of a coordinate RingFlag

The compatible local incidence-chart maps glue over their proved common
principal-open cover. Every global Grassmannian projection is the intrinsic
morphism of the corresponding original quotient step.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory

universe u

variable {A : Type u} [CommRing A] {n : ℕ}
  (F : RingFlag A (Fin n → A) n)

/-- The global classifying map built from the original ring flag. -/
def simultaneousFlagMorphism :
    Spec (CommRingCat.of A) ⟶ selectedFlagChartScheme A n :=
  (simultaneousFlagCoordinateSchemeCover F).glueMorphisms
    (simultaneousFlagLocalMap F) (simultaneousFlagLocalMap_overlap F)

/-- Restriction to each common principal open is its original incidence point. -/
@[reassoc] theorem simultaneousFlagMorphism_local
    (i : SimultaneousFlagCoordinateIndex F) :
    (simultaneousFlagCoordinateSchemeCover F).f i ≫ simultaneousFlagMorphism F =
      simultaneousFlagLocalMap F i :=
  (simultaneousFlagCoordinateSchemeCover F).ι_glueMorphisms
    (simultaneousFlagLocalMap F) (simultaneousFlagLocalMap_overlap F) i

/-- Every projection of the glued map classifies precisely the original
quotient step, with no change to its ambient-coordinate kernel. -/
@[reassoc] theorem simultaneousFlagMorphism_step (j : Fin (n + 1)) :
    simultaneousFlagMorphism F ≫ selectedFlagChartSchemeStep A n j =
      selectedQuotientMorphism A (F.step j) := by
  apply (simultaneousFlagCoordinateSchemeCover F).hom_ext
  intro i
  calc
    _ = simultaneousFlagLocalMap F i ≫ selectedFlagChartSchemeStep A n j := by
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun m => m ≫ selectedFlagChartSchemeStep A n j)
          (simultaneousFlagMorphism_local F i))
    _ = simultaneousFlagIncidencePointMap F i ≫
        selectedFlagIncidenceChartStepMorphism A
          (simultaneousFlagCoordinateSelection F i) j := by
      rw [simultaneousFlagLocalMap, Category.assoc,
        selectedFlagChartSchemeChart_step]
    _ = selectedQuotientMorphism A
        (coordinateGrassmannianBaseChange
          (Localization.Away (simultaneousFlagCoordinateElement F i)) (F.step j)) :=
      simultaneousFlagIncidencePointMap_step F i j
    _ = _ := (selectedQuotientMorphism_baseChange (F.step j)).symm

/-- The global map is a morphism over the original coefficient spectrum. -/
@[reassoc] theorem simultaneousFlagMorphism_toSpec :
    simultaneousFlagMorphism F ≫ selectedFlagChartSchemeToSpec A n =
      𝟙 (Spec (CommRingCat.of A)) := by
  apply (simultaneousFlagCoordinateSchemeCover F).hom_ext
  intro i
  calc
    (simultaneousFlagCoordinateSchemeCover F).f i ≫
        (simultaneousFlagMorphism F ≫ selectedFlagChartSchemeToSpec A n) =
      simultaneousFlagLocalMap F i ≫ selectedFlagChartSchemeToSpec A n := by
        exact (Category.assoc _ _ _).symm.trans
          (congrArg (fun m => m ≫ selectedFlagChartSchemeToSpec A n)
            (simultaneousFlagMorphism_local F i))
    _ = simultaneousFlagIncidencePointMap F i ≫
        selectedFlagIncidenceChartToSpec A
          (simultaneousFlagCoordinateSelection F i) := by
      rw [simultaneousFlagLocalMap, Category.assoc,
        selectedFlagChartSchemeChart_toSpec]
    _ = (simultaneousFlagCoordinateSchemeCover F).f i ≫
        𝟙 (Spec (CommRingCat.of A)) := by
      rw [simultaneousFlagIncidencePointMap_toSpec, Category.comp_id]
      rfl

end FlagVarieties.Foundations.QuotientCharts
