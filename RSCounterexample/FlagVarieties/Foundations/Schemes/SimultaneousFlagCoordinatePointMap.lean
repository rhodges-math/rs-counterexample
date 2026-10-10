import RSCounterexample.FlagVarieties.Foundations.Schemes.SimultaneousFlagCoordinateIncidence
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedFlagIncidenceChart
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedQuotientMorphismPresentation

/-!
# Incidence-chart maps from a given ring flag

The map on each simultaneous principal open is induced by its unique joint
incidence parameters. Its selected-chart step maps classify the original
base-changed quotient kernels.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory

universe u

variable {A : Type u} [CommRing A] {n : ℕ}
  (F : RingFlag A (Fin n → A) n)
  (i : SimultaneousFlagCoordinateIndex F)

/-- Evaluation factors through the full-flag incidence quotient ring. -/
def simultaneousFlagIncidenceEvaluation :
    (MvPolynomial (FlagChartVariable n) A ⧸
      selectedFlagIncidenceIdeal A (simultaneousFlagCoordinateSelection F i)) →ₐ[A]
      Localization.Away (simultaneousFlagCoordinateElement F i) :=
  Ideal.Quotient.liftₐ _ (simultaneousFlagCoordinateEvaluation F i)
    (fun _ hp => simultaneousFlagCoordinateEvaluation_ideal F i hp)

/-- The map from the common principal open into the affine incidence chart. -/
def simultaneousFlagIncidencePointMap :
    Spec (CommRingCat.of (Localization.Away (simultaneousFlagCoordinateElement F i))) ⟶
      selectedFlagIncidenceChart A (simultaneousFlagCoordinateSelection F i) :=
  Spec.map (CommRingCat.ofHom (simultaneousFlagIncidenceEvaluation F i).toRingHom)

/-- The `j`-th selected-chart projection classifies precisely the original
base-changed quotient step, retaining its original coordinate kernel. -/
@[reassoc] theorem simultaneousFlagIncidencePointMap_step (j : Fin (n + 1)) :
    simultaneousFlagIncidencePointMap F i ≫
      selectedFlagIncidenceChartStepMorphism A (simultaneousFlagCoordinateSelection F i) j =
    selectedQuotientMorphism A
      (coordinateGrassmannianBaseChange
        (Localization.Away (simultaneousFlagCoordinateElement F i)) (F.step j)) := by
  rw [← simultaneousFlagCoordinateEvaluation_step F i j,
    show selectedFlagChartStep A (simultaneousFlagCoordinateSelection F i)
      (simultaneousFlagCoordinateEvaluation F i) j =
      selectedChartPoint A (simultaneousFlagCoordinateSelection F i j)
        ((simultaneousFlagCoordinateEvaluation F i).comp
          (selectedFlagChartVariables A j)) from rfl,
    selectedQuotientMorphism_selectedChartPoint]
  unfold simultaneousFlagIncidencePointMap selectedFlagIncidenceChartStepMorphism
    selectedFlagIncidenceChartStep
  rw [← Category.assoc, spec_map_algHom_comp]
  rfl

/-- This affine incidence-chart map is over the localization map. -/
@[reassoc] theorem simultaneousFlagIncidencePointMap_toSpec :
    simultaneousFlagIncidencePointMap F i ≫
      selectedFlagIncidenceChartToSpec A (simultaneousFlagCoordinateSelection F i) =
    Spec.map (CommRingCat.ofHom
      (algebraMap A (Localization.Away (simultaneousFlagCoordinateElement F i)))) := by
  unfold simultaneousFlagIncidencePointMap selectedFlagIncidenceChartToSpec
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (simultaneousFlagIncidenceEvaluation F i).comp_algebraMap

end FlagVarieties.Foundations.QuotientCharts
