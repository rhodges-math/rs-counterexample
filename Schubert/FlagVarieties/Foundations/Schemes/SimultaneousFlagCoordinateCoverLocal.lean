import Schubert.FlagVarieties.Foundations.Schemes.SimultaneousFlagCoordinateCover

/-!
# Original flag quotients on a simultaneous principal refinement

Each product localization receives the selected presentation of every
original quotient step. In particular, the selected coordinate map is
bijection on that same principal open for every step at once.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

universe u

variable {A : Type u} [CommRing A] {n : ℕ}
  (F : RingFlag A (Fin n → A) n)
  (i : SimultaneousFlagCoordinateIndex F)

/-- The selected step denominator becomes a unit in the common localization. -/
theorem simultaneousFlagStepElement_isUnit (j : Fin (n + 1)) :
    IsUnit (algebraMap A (Localization.Away (simultaneousFlagCoordinateElement F i))
      ((flagStepCover F j).element (i j))) := by
  apply IsLocalization.Away.isUnit_of_dvd
    (x := simultaneousFlagCoordinateElement F i)
  exact simultaneousFlagCoordinateElement_dvd F i j

/-- The restriction homomorphism from the step open to the common open. -/
def simultaneousFlagStepToCommon (j : Fin (n + 1)) :
    Localization.Away ((flagStepCover F j).element (i j)) →ₐ[A]
      Localization.Away (simultaneousFlagCoordinateElement F i) :=
  IsLocalization.Away.liftAlgHom ((flagStepCover F j).element (i j))
    (f := IsScalarTower.toAlgHom A A
      (Localization.Away (simultaneousFlagCoordinateElement F i)))
    (simultaneousFlagStepElement_isUnit F i j)

/-- A normalized quotient presentation of the original `j`-th step
over the common principal localization; equality retains its original kernel. -/
theorem simultaneousFlagStep_represents (j : Fin (n + 1)) :
    selectedChartPoint A (simultaneousFlagCoordinateSelection F i j)
      ((simultaneousFlagStepToCommon F i j).comp
        ((flagStepCover F j).evaluation (i j))) =
      coordinateGrassmannianBaseChange
        (Localization.Away (simultaneousFlagCoordinateElement F i)) (F.step j) := by
  exact (flagStepCover F j).represents_after_map (i j)
    (simultaneousFlagStepToCommon F i j)

/-- Every original flag quotient has a selected coordinate basis on the same
principal open, including rank zero and rank `n` endpoint steps. -/
theorem simultaneousFlagStep_selected_bijective (j : Fin (n + 1)) :
    Function.Bijective
      (((coordinateGrassmannianBaseChange
        (Localization.Away (simultaneousFlagCoordinateElement F i))
        (F.step j)).toSubmodule.mkQ).comp
          (coordinateInclusion (simultaneousFlagCoordinateSelection F i j))) := by
  rw [← simultaneousFlagStep_represents F i j]
  exact selectedChartPoint_selected_bijective A
    (simultaneousFlagCoordinateSelection F i j)
    ((simultaneousFlagStepToCommon F i j).comp
      ((flagStepCover F j).evaluation (i j)))

end FlagVarieties.Foundations.QuotientCharts
