import Schubert.FlagVarieties.Foundations.Schemes.SimultaneousFlagCoordinateBaseChange

/-!
# Joint incidence coordinates on each common principal open

The simultaneous selected bases determine one polynomial parameter map.
Its incidence ideal vanishes because the base-changed original kernels are
nested. Every selected step is exactly the corresponding original quotient.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

universe u

variable {A : Type u} [CommRing A] {n : ℕ}
  (F : RingFlag A (Fin n → A) n)
  (i : SimultaneousFlagCoordinateIndex F)

/-- A simultaneous choice gives a unique joint parameter map cutting out
the incidence scheme, with every original localized quotient recovered. -/
theorem simultaneousFlagCoordinate_existsUnique :
    ∃! k : MvPolynomial (FlagChartVariable n) A →ₐ[A]
        Localization.Away (simultaneousFlagCoordinateElement F i),
      selectedFlagIncidenceIdeal A (simultaneousFlagCoordinateSelection F i) ≤
          RingHom.ker k.toRingHom ∧
        ∀ j : Fin (n + 1),
          selectedFlagChartStep A (simultaneousFlagCoordinateSelection F i) k j =
            coordinateGrassmannianBaseChange
              (Localization.Away (simultaneousFlagCoordinateElement F i)) (F.step j) := by
  apply selectedFlagChart_existsUnique A
    (coordinateRingFlagBaseChange
      (B := Localization.Away (simultaneousFlagCoordinateElement F i)) F)
    (simultaneousFlagCoordinateSelection F i)
  intro j
  exact simultaneousFlagStep_selected_bijective F i j

/-- The canonical joint parameters on the common principal open. -/
def simultaneousFlagCoordinateEvaluation :
    MvPolynomial (FlagChartVariable n) A →ₐ[A]
      Localization.Away (simultaneousFlagCoordinateElement F i) :=
  (simultaneousFlagCoordinate_existsUnique F i).exists.choose

/-- All adjacent incidence equations vanish under the parameters. -/
theorem simultaneousFlagCoordinateEvaluation_ideal :
    selectedFlagIncidenceIdeal A (simultaneousFlagCoordinateSelection F i) ≤
      RingHom.ker (simultaneousFlagCoordinateEvaluation F i).toRingHom :=
  (simultaneousFlagCoordinate_existsUnique F i).exists.choose_spec.1

/-- Every joint-parameter step is the original flag quotient after base change. -/
theorem simultaneousFlagCoordinateEvaluation_step (j : Fin (n + 1)) :
    selectedFlagChartStep A (simultaneousFlagCoordinateSelection F i)
      (simultaneousFlagCoordinateEvaluation F i) j =
        coordinateGrassmannianBaseChange
          (Localization.Away (simultaneousFlagCoordinateElement F i)) (F.step j) :=
  (simultaneousFlagCoordinate_existsUnique F i).exists.choose_spec.2 j

/-- Equality of the complete original local flag and the incidence
flag induced by the joint polynomial parameters. -/
theorem simultaneousFlagCoordinateEvaluation_flag :
    selectedFlagChartRingFlag A (simultaneousFlagCoordinateSelection F i)
      (simultaneousFlagCoordinateEvaluation F i)
      (simultaneousFlagCoordinateEvaluation_ideal F i) =
    coordinateRingFlagBaseChange
      (B := Localization.Away (simultaneousFlagCoordinateElement F i)) F := by
  apply RingFlag.ext
  intro j
  exact congrArg Module.Grassmannian.toSubmodule
    (simultaneousFlagCoordinateEvaluation_step F i j)

end FlagVarieties.Foundations.QuotientCharts
