import Schubert.FlagVarieties.Foundations.Schemes.SimultaneousFlagCoordinateMorphism
import Schubert.FlagVarieties.Foundations.Schemes.SelectedFlagChartPointBaseChange

/-!
# Relative coefficient-ring coordinates on the same proved cover

For `R → A`, the same simultaneous principal cover yields joint flag-chart
parameters over `R`. Their quotient steps are the scalar extensions
of the original flag over `A`, with no chosen global basis.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory

universe u

variable (R : Type u) [CommRing R] {A : Type u} [CommRing A]
  [Algebra R A] {n : ℕ}
  (F : RingFlag A (Fin n → A) n)
  (i : SimultaneousFlagCoordinateIndex F)

/-- The original localized flag determines one unique `R`-relative joint
evaluation satisfying all incidence equations. -/
theorem simultaneousFlagRelative_existsUnique :
    ∃! k : MvPolynomial (FlagChartVariable n) R →ₐ[R]
        Localization.Away (simultaneousFlagCoordinateElement F i),
      selectedFlagIncidenceIdeal R (simultaneousFlagCoordinateSelection F i) ≤
          RingHom.ker k.toRingHom ∧
        ∀ j : Fin (n + 1),
          selectedFlagChartStep R (simultaneousFlagCoordinateSelection F i) k j =
            coordinateGrassmannianBaseChange
              (Localization.Away (simultaneousFlagCoordinateElement F i)) (F.step j) := by
  apply selectedFlagChart_existsUnique R
    (coordinateRingFlagBaseChange
      (B := Localization.Away (simultaneousFlagCoordinateElement F i)) F)
    (simultaneousFlagCoordinateSelection F i)
  intro j
  exact simultaneousFlagStep_selected_bijective F i j

/-- Canonical relative joint parameters on the common principal open. -/
def simultaneousFlagRelativeEvaluation :
    MvPolynomial (FlagChartVariable n) R →ₐ[R]
      Localization.Away (simultaneousFlagCoordinateElement F i) :=
  (simultaneousFlagRelative_existsUnique R F i).exists.choose

theorem simultaneousFlagRelativeEvaluation_ideal :
    selectedFlagIncidenceIdeal R (simultaneousFlagCoordinateSelection F i) ≤
      RingHom.ker (simultaneousFlagRelativeEvaluation R F i).toRingHom :=
  (simultaneousFlagRelative_existsUnique R F i).exists.choose_spec.1

theorem simultaneousFlagRelativeEvaluation_step (j : Fin (n + 1)) :
    selectedFlagChartStep R (simultaneousFlagCoordinateSelection F i)
      (simultaneousFlagRelativeEvaluation R F i) j =
        coordinateGrassmannianBaseChange
          (Localization.Away (simultaneousFlagCoordinateElement F i)) (F.step j) :=
  (simultaneousFlagRelative_existsUnique R F i).exists.choose_spec.2 j

/-- A local scheme map to the glued flag scheme over `R`. -/
def simultaneousFlagRelativeLocalMap :
    Spec (CommRingCat.of (Localization.Away (simultaneousFlagCoordinateElement F i))) ⟶
      selectedFlagChartScheme R n :=
  selectedFlagChartPointMap R (simultaneousFlagCoordinateSelection F i)
    (simultaneousFlagRelativeEvaluation R F i)
    (simultaneousFlagRelativeEvaluation_ideal R F i)

@[reassoc] theorem simultaneousFlagRelativeLocalMap_step (j : Fin (n + 1)) :
    simultaneousFlagRelativeLocalMap R F i ≫ selectedFlagChartSchemeStep R n j =
      selectedQuotientMorphism R
        (coordinateGrassmannianBaseChange
          (Localization.Away (simultaneousFlagCoordinateElement F i)) (F.step j)) := by
  rw [simultaneousFlagRelativeLocalMap, selectedFlagChartPointMap_step,
    ← simultaneousFlagRelativeEvaluation_step R F i j]
  change selectedChartPointMap R (simultaneousFlagCoordinateSelection F i j)
      ((simultaneousFlagRelativeEvaluation R F i).comp (selectedFlagChartVariables R j)) =
    selectedQuotientMorphism R
      (selectedChartPoint R (simultaneousFlagCoordinateSelection F i j)
        ((simultaneousFlagRelativeEvaluation R F i).comp (selectedFlagChartVariables R j)))
  exact (selectedQuotientMorphism_selectedChartPoint _ _).symm

@[reassoc] theorem simultaneousFlagRelativeLocalMap_toSpec :
    simultaneousFlagRelativeLocalMap R F i ≫ selectedFlagChartSchemeToSpec R n =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (Localization.Away (simultaneousFlagCoordinateElement F i)))) :=
  selectedFlagChartPointMap_toSpec R
    (simultaneousFlagCoordinateSelection F i)
    (simultaneousFlagRelativeEvaluation R F i)
    (simultaneousFlagRelativeEvaluation_ideal R F i)

end FlagVarieties.Foundations.QuotientCharts
