import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedMatrixActionAffine
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Scheme
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
The varying universal matrix on the relative product of `GLₙ` and
the selected quotient Grassmannian. The coordinate ring is Tau Ceti's
determinant localization; no pointwise family of constant maps is substituted
for this scheme morphism.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ModuleSheafGluing
universe u
variable (R : Type u) [CommRing R] (n d : ℕ)

/-- The product `GLₙ ×_R Gr` of `GLₙ` and the Grassmannian `Gr` of rank-`d` quotients of `𝒪ⁿ`. -/
def generalLinearGrassmannianProduct : Scheme.{u} :=
  pullback (TauCeti.GeneralLinear.groupScheme R n).X.hom
    (selectedChartSchemeToSpec R n d)

/-- The projection `GLₙ ×_R Gr ⟶ GLₙ`. -/
def generalLinearGrassmannianGroup : generalLinearGrassmannianProduct R n d ⟶
    (TauCeti.GeneralLinear.groupScheme R n).X.left :=
  pullback.fst _ _

/-- The projection `GLₙ ×_R Gr ⟶ Gr`. -/
def generalLinearGrassmannianPoint : generalLinearGrassmannianProduct R n d ⟶
    selectedChartScheme R n d :=
  pullback.snd _ _

/-- The structure morphism `GLₙ ×_R Gr ⟶ Spec R`. -/
def generalLinearGrassmannianToSpec : generalLinearGrassmannianProduct R n d ⟶
    Spec (CommRingCat.of R) :=
  generalLinearGrassmannianPoint R n d ≫ selectedChartSchemeToSpec R n d

/-- The projection to `GLₙ`, followed by `GLₙ ≅ Spec 𝒪(GLₙ)`. -/
def generalLinearGrassmannianCoordinateMap : generalLinearGrassmannianProduct R n d ⟶
    Spec (CommRingCat.of (TauCeti.GeneralLinear.CoordinateRing R n)) :=
  generalLinearGrassmannianGroup R n d ≫
    (TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom

/-- The generic invertible matrix over `𝒪(GLₙ)`. -/
def generalLinearGrassmannianMatrix :
    Matrix (Fin n) (Fin n) (TauCeti.GeneralLinear.CoordinateRing R n) :=
  TauCeti.GeneralLinear.localizedGenericMatrix R n

theorem generalLinearGrassmannianMatrix_isUnit :
    IsUnit (generalLinearGrassmannianMatrix R n) := by
  exact (Matrix.isUnit_iff_isUnit_det (generalLinearGrassmannianMatrix R n)).mpr
    (TauCeti.GeneralLinear.isUnit_det_localizedGenericMatrix R n)

/-- The quotient of `𝒪ⁿ` on `GLₙ ×_R Gr`: the pulled-back universal quotient, precomposed with the
automorphism of `𝒪ⁿ` given by the generic matrix. -/
def generalLinearGrassmannianQuotient :
    coordinateFreeSheaf (generalLinearGrassmannianProduct R n d) n ⟶
      (Scheme.Modules.pullback (generalLinearGrassmannianPoint R n d)).obj
        (selectedUniversalQuotientSheaf R n d) :=
  (constantMatrixSheafIso (TauCeti.GeneralLinear.CoordinateRing R n)
    (generalLinearGrassmannianCoordinateMap R n d)
    (generalLinearGrassmannianMatrix R n)
    (generalLinearGrassmannianMatrix_isUnit R n)).inv ≫
      coordinatePullbackQuotient (generalLinearGrassmannianPoint R n d)
        (selectedUniversalQuotient R n d)

instance generalLinearGrassmannianQuotient_epi :
    Epi (generalLinearGrassmannianQuotient R n d) := by
  unfold generalLinearGrassmannianQuotient
  infer_instance

/-- The action `GLₙ ×_R Gr ⟶ Gr`: the classifying morphism of `generalLinearGrassmannianQuotient`.
-/
def generalLinearGrassmannianAction :
    generalLinearGrassmannianProduct R n d ⟶ selectedChartScheme R n d :=
  globalLocallyFreeQuotientMorphism R (generalLinearGrassmannianToSpec R n d)
    (generalLinearGrassmannianQuotient R n d) d
    (coordinateLocalFrames_pullback (generalLinearGrassmannianPoint R n d)
      (selectedUniversalQuotientSheaf R n d) d
      (selectedUniversalQuotient_over_frames R n d))

@[reassoc] theorem generalLinearGrassmannianAction_toSpec :
    generalLinearGrassmannianAction R n d ≫ selectedChartSchemeToSpec R n d =
      generalLinearGrassmannianToSpec R n d :=
  globalLocallyFreeQuotientMorphism_toSpec R _ _ _ _

/-- The pullback of the universal quotient along the action is the target of
`generalLinearGrassmannianQuotient`. -/
def generalLinearGrassmannianActionTargetIso :
    (Scheme.Modules.pullback (generalLinearGrassmannianAction R n d)).obj
      (selectedUniversalQuotientSheaf R n d) ≅
    (Scheme.Modules.pullback (generalLinearGrassmannianPoint R n d)).obj
      (selectedUniversalQuotientSheaf R n d) :=
  globalLocallyFreeUniversalIso R _ _ _ _

@[reassoc] theorem generalLinearGrassmannianActionTargetIso_source :
    coordinatePullbackQuotient (generalLinearGrassmannianAction R n d)
      (selectedUniversalQuotient R n d) ≫
        (generalLinearGrassmannianActionTargetIso R n d).hom =
      generalLinearGrassmannianQuotient R n d :=
  globalLocallyFreeUniversalIso_source R _ _ _ _

/-- The varying morphism classifies the pullback quotient on every
test scheme, with its labelled source unchanged. -/
theorem generalLinearGrassmannianAction_pullback {Y : Scheme.{u}}
    (f : Y ⟶ generalLinearGrassmannianProduct R n d) :
    f ≫ generalLinearGrassmannianAction R n d =
      globalLocallyFreeQuotientMorphism R
        (f ≫ generalLinearGrassmannianToSpec R n d)
        (coordinatePullbackQuotient f (generalLinearGrassmannianQuotient R n d)) d
        (coordinateLocalFrames_pullback f
          ((Scheme.Modules.pullback (generalLinearGrassmannianPoint R n d)).obj
            (selectedUniversalQuotientSheaf R n d)) d
          (coordinateLocalFrames_pullback (generalLinearGrassmannianPoint R n d)
            (selectedUniversalQuotientSheaf R n d) d
            (selectedUniversalQuotient_over_frames R n d))) := by
  exact globalLocallyFreeQuotientMorphism_pullback R _ _ d _ f

end FlagVarieties.Foundations.QuotientCharts
