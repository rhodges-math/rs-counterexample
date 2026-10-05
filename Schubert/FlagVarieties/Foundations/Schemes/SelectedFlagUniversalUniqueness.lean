import Schubert.FlagVarieties.Foundations.Schemes.SelectedFlagGlobalFaithfulness
import Schubert.FlagVarieties.Foundations.Schemes.SelectedFlagUniversalQuotient
import Schubert.FlagVarieties.Foundations.Schemes.SelectedUniversalMorphismUniqueness
import Schubert.FlagVarieties.Foundations.Schemes.CoordinateQuotientPullbackComparison

/-!
# The universal flag determines its classifying morphism

Source-preserving isomorphisms of all quotient steps determine the
scheme morphism. The proof uses the already established Grassmannian
universal property and joint faithfulness of the flag projections.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] {n : ℕ} {X : Scheme.{u}}

/-- For `F : X ⟶ Flₙ`, the pullback of the universal Grassmannian quotient along the step-`j`
projection of `F` is the pullback along `F` of the universal step-`j` quotient. -/
def selectedFlagUniversalProjectionIso (F : X ⟶ selectedFlagChartScheme R n) (j : Fin (n+1)) :
    (Scheme.Modules.pullback (F ≫ selectedFlagChartSchemeStep R n j)).obj
      (selectedUniversalQuotientSheaf R n (n-j.val)) ≅
    (Scheme.Modules.pullback F).obj (selectedFlagUniversalTarget R n j) :=
  coordinateQuotientComparisonPullback F (selectedFlagChartSchemeStep R n j) (Iso.refl _)

@[reassoc]
theorem selectedFlagUniversalProjectionIso_source
    (F : X ⟶ selectedFlagChartScheme R n) (j : Fin (n+1)) :
    coordinatePullbackQuotient (F ≫ selectedFlagChartSchemeStep R n j)
        (selectedUniversalQuotient R n (n-j.val)) ≫
      (selectedFlagUniversalProjectionIso R F j).hom =
        coordinatePullbackQuotient F (selectedFlagUniversalQuotient R n j) :=
  coordinateQuotientComparisonPullback_source F (selectedFlagChartSchemeStep R n j)
    (selectedUniversalQuotient R n (n-j.val)) (selectedFlagUniversalQuotient R n j)
    (Iso.refl _) (Category.comp_id _)

theorem selectedFlagUniversalMorphism_unique
    (F G : X ⟶ selectedFlagChartScheme R n)
    (hbase : F ≫ selectedFlagChartSchemeToSpec R n = G ≫ selectedFlagChartSchemeToSpec R n)
    (e : ∀ j, (Scheme.Modules.pullback F).obj (selectedFlagUniversalTarget R n j) ≅
      (Scheme.Modules.pullback G).obj (selectedFlagUniversalTarget R n j))
    (he : ∀ j, coordinatePullbackQuotient F (selectedFlagUniversalQuotient R n j) ≫
      (e j).hom = coordinatePullbackQuotient G (selectedFlagUniversalQuotient R n j)) :
    F = G := by
  apply selectedFlagMorphism_eq_of_projections_eq R F G
  intro j
  apply selectedUniversalMorphism_unique R
      (F ≫ selectedFlagChartSchemeStep R n j) (G ≫ selectedFlagChartSchemeStep R n j)
      (by simpa only [Category.assoc, selectedFlagChartSchemeStep_toSpec] using hbase)
      (selectedFlagUniversalProjectionIso R F j ≪≫ e j ≪≫
        (selectedFlagUniversalProjectionIso R G j).symm)
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Category.assoc, selectedFlagUniversalProjectionIso_source, he j]
  rw [← selectedFlagUniversalProjectionIso_source R G j]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end FlagVarieties.Foundations.QuotientCharts
