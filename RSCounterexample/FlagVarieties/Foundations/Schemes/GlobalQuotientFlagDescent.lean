import RSCounterexample.FlagVarieties.Foundations.Schemes.GlobalLocallyFreeQuotientDescent
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedFlagUniversalFamily
import RSCounterexample.FlagVarieties.Foundations.Schemes.QuotientFlagFamilyComparison
import RSCounterexample.FlagVarieties.Foundations.Schemes.QuotientFlagFamilyPullback

/-!
# Stepwise global recovery of a quotient-flag family

Local source-preserving comparisons to the flag universal quotients
descend along any open cover. Compatibility is forced by the common
epimorphic labelled source; it is not an additional hypothesis.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory

universe u v

variable (R : Type u) [CommRing R] {X : Scheme.{u}} {n : ℕ}
  (F : QuotientFlagFamily X n) (C : X.OpenCover.{v})
  (f : ∀ i, C.X i ⟶ selectedFlagChartScheme R n)
  (e : ∀ i j, (Scheme.Modules.pullback (f i)).obj
      (selectedFlagUniversalTarget R n j) ≅
    (Scheme.Modules.pullback (C.f i)).obj (F.target j))
  (he : ∀ i j, coordinatePullbackQuotient (f i)
      (selectedFlagUniversalQuotient R n j) ≫ (e i j).hom =
    coordinatePullbackQuotient (C.f i) (F.quotient j))
  (g : X ⟶ selectedFlagChartScheme R n)
  (hg : ∀ i, C.f i ≫ g = f i)

/-- The target comparison on one cover member, transported through
pullback composition and the equality of local classifying maps. -/
def selectedFlagUniversalLocalComparison (i : C.I₀) (j : Fin (n + 1)) :
    (Scheme.Modules.pullback (C.f i)).obj
      ((Scheme.Modules.pullback g).obj (selectedFlagUniversalTarget R n j)) ≅
    (Scheme.Modules.pullback (C.f i)).obj (F.target j) :=
  (Scheme.Modules.pullbackComp (C.f i) g).app
      (selectedFlagUniversalTarget R n j) ≪≫
    (Scheme.Modules.pullbackCongr (hg i)).app
      (selectedFlagUniversalTarget R n j) ≪≫ e i j

include he

/-- The transported local comparison preserves the original rank-`n`
labelled free-source quotient map exactly. -/
theorem selectedFlagUniversalLocalComparison_source (i : C.I₀)
    (j : Fin (n + 1)) :
    coordinatePullbackQuotient (C.f i)
        (coordinatePullbackQuotient g (selectedFlagUniversalQuotient R n j)) ≫
      (selectedFlagUniversalLocalComparison R F C f e g hg i j).hom =
        coordinatePullbackQuotient (C.f i) (F.quotient j) :=
  coordinatePullbackQuotient_transport (C.f i) g (hg i)
    (selectedFlagUniversalQuotient R n j) (e i j)
    (coordinatePullbackQuotient (C.f i) (F.quotient j)) (he i j)

/-- The universal target at step `j` recovers the original global
target sheaf, with compatibility derived from epimorphic quotients. -/
def selectedFlagUniversalIsoOfLocal (j : Fin (n + 1)) :
    (Scheme.Modules.pullback g).obj (selectedFlagUniversalTarget R n j) ≅
      F.target j := by
  letI : Epi (F.quotient j) := F.quotient_epi j
  exact coordinateQuotientIsoOfCover C
    (coordinatePullbackQuotient g (selectedFlagUniversalQuotient R n j))
    (F.quotient j)
    (fun i => selectedFlagUniversalLocalComparison R F C f e g hg i j)
    (fun i => selectedFlagUniversalLocalComparison_source R F C f e he g hg i j)

/-- Exact recovery of the original quotient arrow from the labelled free
source, without an extra overlap compatibility premise. -/
@[reassoc] theorem selectedFlagUniversalIsoOfLocal_source (j : Fin (n + 1)) :
    coordinatePullbackQuotient g (selectedFlagUniversalQuotient R n j) ≫
      (selectedFlagUniversalIsoOfLocal R F C f e he g hg j).hom =
        F.quotient j := by
  letI : Epi (F.quotient j) := F.quotient_epi j
  exact coordinateQuotientIsoOfCover_source C _ (F.quotient j) _ _

/-- The descended step comparisons recover every original adjacent factor.
This follows from their common epimorphic labelled source. -/
@[reassoc] theorem selectedFlagUniversalIsoOfLocal_transition (j : Fin n) :
    (Scheme.Modules.pullback g).map (selectedFlagUniversalTransition R n j) ≫
      (selectedFlagUniversalIsoOfLocal R F C f e he g hg j.succ).hom =
    (selectedFlagUniversalIsoOfLocal R F C f e he g hg j.castSucc).hom ≫
      F.transition j := by
  let U := (selectedFlagUniversalFamily R n).pullback g
  have h := QuotientFlagFamily.transition_natural_of_source U F
    (fun k => (selectedFlagUniversalIsoOfLocal R F C f e he g hg k).hom)
    (selectedFlagUniversalIsoOfLocal_source R F C f e he g hg) j
  exact h

end FlagVarieties.Foundations.QuotientCharts
