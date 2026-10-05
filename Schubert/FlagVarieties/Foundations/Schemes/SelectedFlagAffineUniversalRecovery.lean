import Schubert.FlagVarieties.Foundations.Schemes.SelectedFlagUniversalUniqueness
import Schubert.FlagVarieties.Foundations.Schemes.SelectedUniversalAffineQuotientComparison
import Schubert.FlagVarieties.Foundations.Schemes.AffineQuotientFlagRecovery
import Schubert.FlagVarieties.Foundations.Schemes.PullbackQuotientTransport

/-!
# Recovering original affine flag quotients from their classifying projections

These comparison lemmas retain the coordinate quotient kernels and
the original labelled free-source morphisms. The flag morphism itself is
constructed in `Schemes/SimultaneousFlagCoordinateRelativeMorphism.lean`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] (A : CommRingCat.{u}) [Algebra R A] {n : ℕ}
  (P : RingFlag A (Fin n → A) n)
  (f : Spec A ⟶ selectedFlagChartScheme R n)
  (hf : ∀ j, f ≫ selectedFlagChartSchemeStep R n j = selectedQuotientMorphism R (P.step j))

/-- The pullback along `f` of the universal step-`j` quotient, identified with the quotient of step
`j` of the flag `P`. -/
def selectedFlagAffineStepIso (j : Fin (n+1)) :
    (Scheme.Modules.pullback f).obj (selectedFlagUniversalTarget R n j) ≅
      coordinateQuotientSheaf A (P.step j) :=
  (Scheme.Modules.pullbackComp f (selectedFlagChartSchemeStep R n j)).app
      (selectedUniversalQuotientSheaf R n (n-j.val)) ≪≫
    (Scheme.Modules.pullbackCongr (hf j)).app (selectedUniversalQuotientSheaf R n (n-j.val)) ≪≫
    selectedUniversalAffineQuotientIso R A (P.step j)

@[reassoc]
theorem selectedFlagAffineStepIso_source (j : Fin (n+1)) :
    coordinatePullbackQuotient f (selectedFlagUniversalQuotient R n j) ≫
      (selectedFlagAffineStepIso R A P f hf j).hom = coordinateQuotientSheafMap A (P.step j) :=
  coordinatePullbackQuotient_transport f (selectedFlagChartSchemeStep R n j) (hf j)
    (selectedUniversalQuotient R n (n-j.val)) (selectedUniversalAffineQuotientIso R A (P.step j))
    (coordinateQuotientSheafMap A (P.step j))
    (selectedUniversalAffineQuotientIso_source R A (P.step j))

variable (F : QuotientFlagFamily (Spec A) n)
  (hF : ∀ j, f ≫ selectedFlagChartSchemeStep R n j =
    selectedQuotientMorphism R ((F.toRingFlag A).step j))

/-- The pullback along `f` of the universal step-`j` quotient, identified with the step-`j` quotient
of the family `F`. -/
def selectedFlagAffineFamilyIso (j : Fin (n+1)) :
    (Scheme.Modules.pullback f).obj (selectedFlagUniversalTarget R n j) ≅ F.target j :=
  selectedFlagAffineStepIso R A (F.toRingFlag A) f hF j ≪≫ F.affineStepSheafIso A j

@[reassoc]
theorem selectedFlagAffineFamilyIso_source (j : Fin (n+1)) :
    coordinatePullbackQuotient f (selectedFlagUniversalQuotient R n j) ≫
      (selectedFlagAffineFamilyIso R A f F hF j).hom = F.quotient j := by
  simp only [selectedFlagAffineFamilyIso, Iso.trans_hom]
  rw [← Category.assoc, selectedFlagAffineStepIso_source, F.affineStepSheafIso_source]

end FlagVarieties.Foundations.QuotientCharts
