import Schubert.FlagVarieties.Foundations.Schemes.GeneralLinearGrassmannian
import Schubert.FlagVarieties.Foundations.Schemes.SelectedFlagMatrixAction

/-! The varying universal matrix on the relative product of `GLₙ`
and the selected complete-flag scheme. Its quotient chain uses the original
universal targets and transitions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : Type u) [CommRing R] (n : ℕ)

/-- The product `GLₙ ×_R Flₙ`. -/
def generalLinearFlagProduct : Scheme.{u} :=
  pullback (TauCeti.GeneralLinear.groupScheme R n).X.hom
    (selectedFlagChartSchemeToSpec R n)

/-- The projection `GLₙ ×_R Flₙ ⟶ GLₙ`. -/
def generalLinearFlagGroup : generalLinearFlagProduct R n ⟶
    (TauCeti.GeneralLinear.groupScheme R n).X.left :=
  pullback.fst _ _

/-- The projection `GLₙ ×_R Flₙ ⟶ Flₙ`. -/
def generalLinearFlagPoint : generalLinearFlagProduct R n ⟶
    selectedFlagChartScheme R n :=
  pullback.snd _ _

/-- The structure morphism `GLₙ ×_R Flₙ ⟶ Spec R`. -/
def generalLinearFlagToSpec : generalLinearFlagProduct R n ⟶
    Spec (CommRingCat.of R) :=
  generalLinearFlagPoint R n ≫ selectedFlagChartSchemeToSpec R n

/-- The projection to `GLₙ`, followed by `GLₙ ≅ Spec 𝒪(GLₙ)`. -/
def generalLinearFlagCoordinateMap : generalLinearFlagProduct R n ⟶
    Spec (CommRingCat.of (TauCeti.GeneralLinear.CoordinateRing R n)) :=
  generalLinearFlagGroup R n ≫
    (TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom

/-- The family of quotient flags `g · V•` on `GLₙ ×_R Flₙ`: the pullback of the universal flag,
transported by the generic matrix. -/
def generalLinearFlagFamily : QuotientFlagFamily (generalLinearFlagProduct R n) n :=
  ((selectedFlagUniversalFamily R n).pullback (generalLinearFlagPoint R n)).matrixTransport
    (TauCeti.GeneralLinear.CoordinateRing R n)
    (generalLinearFlagCoordinateMap R n)
    (TauCeti.GeneralLinear.localizedGenericMatrix R n)
    (generalLinearGrassmannianMatrix_isUnit R n)

/-- The action `GLₙ ×_R Flₙ ⟶ Flₙ`, `(g, V•) ↦ g · V•`: the classifying morphism of
`generalLinearFlagFamily`. -/
def generalLinearFlagAction : generalLinearFlagProduct R n ⟶
    selectedFlagChartScheme R n :=
  globalQuotientFlagMorphism R (generalLinearFlagToSpec R n)
    (generalLinearFlagFamily R n)

@[reassoc] theorem generalLinearFlagAction_toSpec :
    generalLinearFlagAction R n ≫ selectedFlagChartSchemeToSpec R n =
      generalLinearFlagToSpec R n :=
  globalQuotientFlagMorphism_toSpec R _ _

/-- The pullback of the universal step-`j` quotient along the action is the step-`j` quotient of
`generalLinearFlagFamily`. -/
def generalLinearFlagActionTargetIso (j : Fin (n+1)) :
    (Scheme.Modules.pullback (generalLinearFlagAction R n)).obj
      (selectedFlagUniversalTarget R n j) ≅
    (generalLinearFlagFamily R n).target j :=
  globalQuotientFlagUniversalIso R _ _ j

@[reassoc] theorem generalLinearFlagActionTargetIso_source (j : Fin (n+1)) :
    coordinatePullbackQuotient (generalLinearFlagAction R n)
      (selectedFlagUniversalQuotient R n j) ≫
        (generalLinearFlagActionTargetIso R n j).hom =
      (generalLinearFlagFamily R n).quotient j :=
  globalQuotientFlagUniversalIso_source R _ _ j

end FlagVarieties.Foundations.QuotientCharts
