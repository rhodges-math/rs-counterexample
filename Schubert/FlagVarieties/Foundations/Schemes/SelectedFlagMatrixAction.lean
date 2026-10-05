import Schubert.FlagVarieties.Foundations.Schemes.QuotientFlagMatrixTransport
import Schubert.FlagVarieties.Foundations.Schemes.GlobalQuotientFlagNaturality

/-!
# The constant matrix action on the complete-flag scheme

Transport the universal quotient flag by the inverse matrix on its labelled
source, and classify that family. This constructs a scheme morphism, with
its structure-sheaf maps and its action on all test schemes.
-/

noncomputable section
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] {n : ℕ}
  (L : Matrix (Fin n) (Fin n) R) (hL : IsUnit L)

/-- The scheme morphism induced by the matrix on each flag subspace. -/
def selectedFlagMatrixAction :
    selectedFlagChartScheme R n ⟶ selectedFlagChartScheme R n :=
  globalQuotientFlagMorphism R (selectedFlagChartSchemeToSpec R n)
    ((selectedFlagUniversalFamily R n).matrixTransport R
      (selectedFlagChartSchemeToSpec R n) L hL)

@[reassoc] theorem selectedFlagMatrixAction_toSpec :
    selectedFlagMatrixAction R L hL ≫ selectedFlagChartSchemeToSpec R n =
      selectedFlagChartSchemeToSpec R n :=
  globalQuotientFlagMorphism_toSpec R _ _

/-- Universal target comparison for the transported source. -/
def selectedFlagMatrixActionTargetIso (j : Fin (n+1)) :
    (Scheme.Modules.pullback (selectedFlagMatrixAction R L hL)).obj
      (selectedFlagUniversalTarget R n j) ≅ selectedFlagUniversalTarget R n j :=
  globalQuotientFlagUniversalIso R _ _ j

@[reassoc] theorem selectedFlagMatrixActionTargetIso_source (j : Fin (n+1)) :
    coordinatePullbackQuotient (selectedFlagMatrixAction R L hL)
        (selectedFlagUniversalQuotient R n j) ≫
      (selectedFlagMatrixActionTargetIso R L hL j).hom =
    (constantMatrixSheafIso R (selectedFlagChartSchemeToSpec R n) L hL).inv ≫
      selectedFlagUniversalQuotient R n j :=
  globalQuotientFlagUniversalIso_source R _ _ j

/-- Arbitrary test morphisms pull back the transported universal family. -/
theorem selectedFlagMatrixAction_pullback {X : Scheme.{u}}
    (p : X ⟶ selectedFlagChartScheme R n) :
    p ≫ selectedFlagMatrixAction R L hL =
      globalQuotientFlagMorphism R (p ≫ selectedFlagChartSchemeToSpec R n)
        (((selectedFlagUniversalFamily R n).matrixTransport R
          (selectedFlagChartSchemeToSpec R n) L hL).pullback p) :=
  globalQuotientFlagMorphism_pullback R _ _ p

end FlagVarieties.Foundations.QuotientCharts
