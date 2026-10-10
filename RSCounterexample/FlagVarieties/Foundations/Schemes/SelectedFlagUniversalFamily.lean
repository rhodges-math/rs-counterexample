import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedFlagUniversalChart
import RSCounterexample.FlagVarieties.Foundations.Schemes.LocalQuotientFactorPullback
import RSCounterexample.FlagVarieties.Foundations.Schemes.QuotientFlagFamilyInitial
import RSCounterexample.FlagVarieties.Foundations.Schemes.QuotientFlagFamilyEndpoints

/-!
# The universal quotient-sheaf flag on the glued incidence scheme

The adjacent morphisms descend from the matrix factors on the open
incidence charts. Their compatibility follows from the global quotient epis.
All quotient ranks and both endpoints are proved, not supplied as assumptions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : Type u) [CommRing R] (n : ℕ)

/-- Descend the adjacent chart factors through the common-source epi. -/
def selectedFlagUniversalTransition (j : Fin n) :
    selectedFlagUniversalTarget R n j.castSucc ⟶ selectedFlagUniversalTarget R n j.succ :=
  ModuleSheafGluing.localPullbackQuotientFactor (selectedFlagChartGlueData R n).openCover
    (selectedFlagUniversalQuotient R n j.castSucc) (selectedFlagUniversalQuotient R n j.succ)
    (fun a => selectedFlagUniversalChartTransition R a.down j)
    (fun a => selectedFlagUniversalChartTransition_pullback_source R a.down j)

@[reassoc]
theorem selectedFlagUniversalTransition_source (j : Fin n) :
    selectedFlagUniversalQuotient R n j.castSucc ≫ selectedFlagUniversalTransition R n j =
      selectedFlagUniversalQuotient R n j.succ :=
  ModuleSheafGluing.localPullbackQuotientFactor_source _ _ _ _ _

/-- The descended map recovers the original factor on every incidence chart. -/
theorem selectedFlagUniversalTransition_chart
    (a : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n) (j : Fin n) :
    (Scheme.Modules.pullback (selectedFlagChartSchemeChart R n a)).map
      (selectedFlagUniversalTransition R n j) = selectedFlagUniversalChartTransition R a j := by
  let : Epi (selectedFlagUniversalQuotient R n j.castSucc) :=
    selectedFlagUniversalQuotient_epi R n j.castSucc
  exact ModuleSheafGluing.localPullbackQuotientFactor_local
    (selectedFlagChartGlueData R n).openCover
    (selectedFlagUniversalQuotient R n j.castSucc) (selectedFlagUniversalQuotient R n j.succ)
    (fun b => selectedFlagUniversalChartTransition R b.down j)
    (fun b => selectedFlagUniversalChartTransition_pullback_source R b.down j) (ULift.up a)

/-- The universal complete quotient flag, with all adjacent maps derived. -/
def selectedFlagUniversalFamily : QuotientFlagFamily (selectedFlagChartScheme R n) n where
  target := selectedFlagUniversalTarget R n
  quotient := selectedFlagUniversalQuotient R n
  quotient_epi := selectedFlagUniversalQuotient_epi R n
  local_frames := selectedFlagUniversalTarget_local_frames R n
  transition := selectedFlagUniversalTransition R n
  transition_source := selectedFlagUniversalTransition_source R n

theorem selectedFlagUniversalQuotient_initial_isIso : IsIso (selectedFlagUniversalQuotient R n 0) :=
  (selectedFlagUniversalFamily R n).initial_quotient_isIso

theorem selectedFlagUniversalTarget_last_isZero :
    IsZero (selectedFlagUniversalTarget R n (Fin.last n)) :=
  (selectedFlagUniversalFamily R n).last_target_isZero

end FlagVarieties.Foundations.QuotientCharts
