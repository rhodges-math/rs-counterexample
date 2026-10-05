import Schubert.FlagVarieties.Foundations.Schemes.SelectedFlagUniversalQuotient
import Schubert.FlagVarieties.Foundations.Schemes.SelectedFlagIncidenceUniversalStep
import Schubert.FlagVarieties.Foundations.Schemes.PullbackQuotientTransport

/-!
# Chart frames and adjacent factors of the global flag quotients

The global quotient targets pull back to the original normalized matrix
targets. Their local adjacent maps preserve the same labelled source.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] {n : ℕ}
  (a : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)

/-- On the chart `a`, the pullback of the universal step-`j` quotient is free of rank `n - j`. -/
def selectedFlagUniversalChartIso (j : Fin (n+1)) :
    (Scheme.Modules.pullback (selectedFlagChartSchemeChart R n a)).obj
      (selectedFlagUniversalTarget R n j) ≅
      coordinateFreeSheaf (selectedFlagIncidenceChart R a) (n-j.val) :=
  (Scheme.Modules.pullbackComp (selectedFlagChartSchemeChart R n a)
    (selectedFlagChartSchemeStep R n j)).app (selectedUniversalQuotientSheaf R n (n-j.val)) ≪≫
  (Scheme.Modules.pullbackCongr (selectedFlagChartSchemeChart_step R n a j)).app
    (selectedUniversalQuotientSheaf R n (n-j.val)) ≪≫ selectedFlagIncidenceUniversalStepIso R a j

@[reassoc]
theorem selectedFlagUniversalChartIso_source (j : Fin (n+1)) :
    coordinatePullbackQuotient (selectedFlagChartSchemeChart R n a)
      (selectedFlagUniversalQuotient R n j) ≫ (selectedFlagUniversalChartIso R a j).hom =
      selectedFlagIncidenceSheafQuotient R a j :=
  coordinatePullbackQuotient_transport (selectedFlagChartSchemeChart R n a)
    (selectedFlagChartSchemeStep R n j) (selectedFlagChartSchemeChart_step R n a j)
    (selectedUniversalQuotient R n (n-j.val)) (selectedFlagIncidenceUniversalStepIso R a j)
    (selectedFlagIncidenceSheafQuotient R a j) (selectedFlagIncidenceUniversalStepIso_source R a j)

/-- The adjacent factor on a chart is the original matrix factor in the chart frames. -/
def selectedFlagUniversalChartTransition (j : Fin n) :
    (Scheme.Modules.pullback (selectedFlagChartSchemeChart R n a)).obj
      (selectedFlagUniversalTarget R n j.castSucc) ⟶
    (Scheme.Modules.pullback (selectedFlagChartSchemeChart R n a)).obj
      (selectedFlagUniversalTarget R n j.succ) :=
  (selectedFlagUniversalChartIso R a j.castSucc).hom ≫
    selectedFlagIncidenceSheafTransition R a j ≫ (selectedFlagUniversalChartIso R a j.succ).inv

@[reassoc]
theorem selectedFlagUniversalChartTransition_source (j : Fin n) :
    coordinatePullbackQuotient (selectedFlagChartSchemeChart R n a)
      (selectedFlagUniversalQuotient R n j.castSucc) ≫ selectedFlagUniversalChartTransition R a j =
    coordinatePullbackQuotient (selectedFlagChartSchemeChart R n a)
      (selectedFlagUniversalQuotient R n j.succ) := by
  apply (cancel_mono (selectedFlagUniversalChartIso R a j.succ).hom).mp
  simp only [selectedFlagUniversalChartTransition, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, selectedFlagUniversalChartIso_source,
    selectedFlagIncidenceSheafTransition_source, selectedFlagUniversalChartIso_source]

/-- The same incidence equation for the pullback functor, before source normalization. -/
theorem selectedFlagUniversalChartTransition_pullback_source (j : Fin n) :
    (Scheme.Modules.pullback (selectedFlagChartSchemeChart R n a)).map
      (selectedFlagUniversalQuotient R n j.castSucc) ≫ selectedFlagUniversalChartTransition R a j =
    (Scheme.Modules.pullback (selectedFlagChartSchemeChart R n a)).map
      (selectedFlagUniversalQuotient R n j.succ) := by
  apply (cancel_epi (coordinatePullbackFreeIso (selectedFlagChartSchemeChart R n a) n).inv).mp
  rw [← Category.assoc]
  exact selectedFlagUniversalChartTransition_source R a j

end FlagVarieties.Foundations.QuotientCharts
