import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedUniversalAffineQuotientComparison
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedAffineClassification

/-!
# The universal quotient on every incoming affine morphism

The earlier affine morphism classification recovers a coordinate kernel
from an arbitrary morphism over the coefficient base. The pullback
of the universal sheaf is its associated quotient, with the original
labelled source preserved.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {n d : ℕ}
  (F : Spec (CommRingCat.of A) ⟶ selectedChartScheme R n d)
  (hF : F ≫ selectedChartSchemeToSpec R n d =
    Spec.map (CommRingCat.ofHom (algebraMap R A)))

/-- The universal pullback is the quotient recovered from the morphism. -/
def selectedUniversalAffineMorphismIso :
    (Scheme.Modules.pullback F).obj (selectedUniversalQuotientSheaf R n d) ≅
      coordinateQuotientSheaf (CommRingCat.of A) (quotientOfSelectedMorphism F hF) :=
  (Scheme.Modules.pullbackCongr
    (selectedQuotientMorphism_quotientOfSelectedMorphism F hF).symm).app
      (selectedUniversalQuotientSheaf R n d) ≪≫
    selectedUniversalAffineQuotientIso R A (quotientOfSelectedMorphism F hF)

@[reassoc]
theorem selectedUniversalAffineMorphismIso_source :
    coordinatePullbackQuotient F (selectedUniversalQuotient R n d) ≫
      (selectedUniversalAffineMorphismIso F hF).hom =
    coordinateQuotientSheafMap (CommRingCat.of A) (quotientOfSelectedMorphism F hF) := by
  unfold selectedUniversalAffineMorphismIso
  simp only [Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, coordinatePullbackQuotient_congr]
  exact selectedUniversalAffineQuotientIso_source R A (quotientOfSelectedMorphism F hF)

end FlagVarieties.Foundations.QuotientCharts
