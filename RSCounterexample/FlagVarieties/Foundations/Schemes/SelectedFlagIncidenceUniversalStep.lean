import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedFlagIncidenceSheafFamily
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedUniversalAffineChart

/-!
# Universal Grassmannian quotients on a full flag incidence chart

At each step, the existing constructed universal quotient pulls back along
the step morphism to the normalized matrix quotient sheaf
on the full incidence chart. The comparison preserves the labelled
rank-`n` source map exactly.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u

variable (R : Type u) [CommRing R] {n : ℕ}
  (a : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)

/-- The universal quotient target on the `j`-th Grassmannian pulls
back to the free target of the full-flag matrix chart. -/
def selectedFlagIncidenceUniversalStepIso (j : Fin (n+1)) :
    (Scheme.Modules.pullback (selectedFlagIncidenceChartStepMorphism R a j)).obj
      (selectedUniversalQuotientSheaf R n (n-j.val)) ≅
      coordinateFreeSheaf (selectedFlagIncidenceChart R a) (n-j.val) :=
  selectedUniversalAffineChartFrame R (a j)
    (CommRingCat.of (selectedFlagIncidenceRing R a))
    (selectedFlagIncidenceStepEval R a j)

/-- This comparison retains the original labelled source equation. -/
@[reassoc]
theorem selectedFlagIncidenceUniversalStepIso_source (j : Fin (n+1)) :
    coordinatePullbackQuotient (selectedFlagIncidenceChartStepMorphism R a j)
      (selectedUniversalQuotient R n (n-j.val)) ≫
      (selectedFlagIncidenceUniversalStepIso R a j).hom =
      selectedFlagIncidenceSheafQuotient R a j := by
  change coordinatePullbackQuotient
      (selectedChartPointMap R (a j) (selectedFlagIncidenceStepEval R a j))
      (selectedUniversalQuotient R n (n-j.val)) ≫
      (selectedUniversalAffineChartFrame R (a j)
        (CommRingCat.of (selectedFlagIncidenceRing R a))
        (selectedFlagIncidenceStepEval R a j)).hom =
      selectedPresentationSheafMap R
        (CommRingCat.of (selectedFlagIncidenceRing R a)) (a j)
        (selectedFlagIncidenceStepEval R a j)
  exact selectedUniversalAffineChartFrame_source R (a j)
    (CommRingCat.of (selectedFlagIncidenceRing R a))
    (selectedFlagIncidenceStepEval R a j)

end FlagVarieties.Foundations.QuotientCharts
