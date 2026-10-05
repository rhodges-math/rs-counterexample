import Schubert.FlagVarieties.Foundations.Schemes.GlobalLocallyFreeQuotientNaturality
import Schubert.FlagVarieties.Foundations.Schemes.SelectedFlagMatrixActionNaturality

/-!
The constant matrix morphism of the quotient Grassmannian. Its
universal quotient is precomposed by the inverse matrix, so its kernel
transforms by the matrix itself. The source maps and arbitrary scheme
pullbacks are retained. The varying universal matrix is
`Schemes/GeneralLinearGrassmannian.lean`, with its group-action laws in
`Schemes/GeneralLinearGrassmannianLawsAffine.lean` and
`Schemes/GeneralLinearGrassmannianLawsGroup.lean`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory ModuleSheafGluing
universe u
variable (R : Type u) [CommRing R] {n : ℕ} (d : ℕ)
  (L : Matrix (Fin n) (Fin n) R) (hL : IsUnit L)

/-- The morphism classifying the transported original universal quotient. -/
def selectedMatrixAction : selectedChartScheme R n d ⟶ selectedChartScheme R n d :=
  globalLocallyFreeQuotientMorphism R (selectedChartSchemeToSpec R n d)
    ((constantMatrixSheafIso R (selectedChartSchemeToSpec R n d) L hL).inv ≫
      selectedUniversalQuotient R n d) d
    (selectedUniversalQuotient_over_frames R n d)

@[reassoc] theorem selectedMatrixAction_toSpec :
    selectedMatrixAction R d L hL ≫ selectedChartSchemeToSpec R n d =
      selectedChartSchemeToSpec R n d :=
  globalLocallyFreeQuotientMorphism_toSpec R _ _ _ _

/-- The transformed universal target is the original quotient target. -/
def selectedMatrixActionTargetIso :
    (Scheme.Modules.pullback (selectedMatrixAction R d L hL)).obj
      (selectedUniversalQuotientSheaf R n d) ≅ selectedUniversalQuotientSheaf R n d :=
  globalLocallyFreeUniversalIso R _ _ _ _

@[reassoc] theorem selectedMatrixActionTargetIso_source :
    coordinatePullbackQuotient (selectedMatrixAction R d L hL)
      (selectedUniversalQuotient R n d) ≫
        (selectedMatrixActionTargetIso R d L hL).hom =
      (constantMatrixSheafIso R (selectedChartSchemeToSpec R n d) L hL).inv ≫
        selectedUniversalQuotient R n d :=
  globalLocallyFreeUniversalIso_source R _ _ _ _

/-- On every test scheme, the morphism classifies the transported pullback
of the original universal quotient, with its original labelled source. -/
theorem selectedMatrixAction_pullback {X : Scheme.{u}}
    (p : X ⟶ selectedChartScheme R n d) :
    p ≫ selectedMatrixAction R d L hL =
      globalLocallyFreeQuotientMorphism R (p ≫ selectedChartSchemeToSpec R n d)
        ((constantMatrixSheafIso R (p ≫ selectedChartSchemeToSpec R n d) L hL).inv ≫
          coordinatePullbackQuotient p (selectedUniversalQuotient R n d)) d
        (coordinateLocalFrames_pullback p (selectedUniversalQuotientSheaf R n d) d
          (selectedUniversalQuotient_over_frames R n d)) := by
  unfold selectedMatrixAction
  rw [globalLocallyFreeQuotientMorphism_pullback]
  simp only [coordinatePullbackQuotient_constantMatrix_inv]

end FlagVarieties.Foundations.QuotientCharts
