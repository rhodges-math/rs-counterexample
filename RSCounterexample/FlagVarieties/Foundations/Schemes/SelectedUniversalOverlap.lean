import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedUniversalChart
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedChartPointMaps

/-!
# The determinant overlap is the chart intersection

The scheme-gluing pullback theorem identifies the determinant-localized
spectrum with the intersection of the two range opens. Both projection
identities are retained, so quotient sheaf comparisons can be transported
to the intersection without assuming an affine-overlap presentation.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

variable (R : Type u) [CommRing R] {n d : ℕ} (a b : Fin d ↪ Fin n)

/-- The determinant overlap is the pullback of the two original chart maps. -/
theorem selectedChartOverlap_isPullback :
    IsPullback (selectedChartOverlapInclusion R a b) (selectedChartOverlapMap R a b)
      (selectedChartSchemeChart R n d a) (selectedChartSchemeChart R n d b) := by
  have h := IsPullback.of_isLimit ((selectedChartGlueData R n d).vPullbackConeIsLimit ⟨a⟩ ⟨b⟩)
  change IsPullback (selectedChartOverlapInclusion R a b)
    ((selectedChartOverlapIso R a b).hom ≫ selectedChartOverlapInclusion R b a)
      (selectedChartSchemeChart R n d a) (selectedChartSchemeChart R n d b) at h
  rw [selectedChartOverlapIso_hom_inclusion] at h
  exact h

/-- Replacing each chart by its range open retains the pullback square. -/
theorem selectedUniversalOverlap_isPullback :
    IsPullback
      (selectedChartOverlapInclusion R a b ≫ (selectedUniversalOpenIso R n d a).hom)
      (selectedChartOverlapMap R a b ≫ (selectedUniversalOpenIso R n d b).hom)
      (selectedUniversalOpen R n d a).ι (selectedUniversalOpen R n d b).ι := by
  apply (selectedChartOverlap_isPullback R a b).of_iso (Iso.refl _)
    (selectedUniversalOpenIso R n d a) (selectedUniversalOpenIso R n d b) (Iso.refl _)
  · simp
  · simp
  · change selectedChartSchemeChart R n d a =
      (selectedChartSchemeChart R n d a).isoOpensRange.hom ≫
        (selectedChartSchemeChart R n d a).opensRange.ι
    exact (Scheme.Hom.isoOpensRange_hom_ι (selectedChartSchemeChart R n d a)).symm
  · change selectedChartSchemeChart R n d b =
      (selectedChartSchemeChart R n d b).isoOpensRange.hom ≫
        (selectedChartSchemeChart R n d b).opensRange.ι
    exact (Scheme.Hom.isoOpensRange_hom_ι (selectedChartSchemeChart R n d b)).symm

/-- The determinant-localized scheme is isomorphic to the full intersection open. -/
def selectedUniversalOverlapIso :
    Spec (CommRingCat.of (Localization.Away (selectedPolynomialBlock R a b).det)) ≅
      (selectedUniversalOpen R n d a ⊓ selectedUniversalOpen R n d b).toScheme :=
  (selectedUniversalOverlap_isPullback R a b).isoIsPullback _ _
    (isPullback_opens_inf (selectedUniversalOpen R n d a) (selectedUniversalOpen R n d b))

@[reassoc] theorem selectedUniversalOverlapIso_first :
    (selectedUniversalOverlapIso R a b).hom ≫
        (selectedChartScheme R n d).homOfLE inf_le_left =
      selectedChartOverlapInclusion R a b ≫ (selectedUniversalOpenIso R n d a).hom :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

@[reassoc] theorem selectedUniversalOverlapIso_second :
    (selectedUniversalOverlapIso R a b).hom ≫
        (selectedChartScheme R n d).homOfLE inf_le_right =
      selectedChartOverlapMap R a b ≫ (selectedUniversalOpenIso R n d b).hom :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- The first coordinate map on the overlap is exactly the localization inclusion. -/
@[reassoc] theorem selectedUniversalOverlapIso_first_chart :
    (selectedUniversalOverlapIso R a b).hom ≫
        (selectedChartScheme R n d).homOfLE inf_le_left ≫
          (selectedUniversalOpenIso R n d a).inv = selectedChartOverlapInclusion R a b := by
  rw [← Category.assoc, selectedUniversalOverlapIso_first]
  simp

/-- The second coordinate map is exactly the original regular matrix transition. -/
@[reassoc] theorem selectedUniversalOverlapIso_second_chart :
    (selectedUniversalOverlapIso R a b).hom ≫
        (selectedChartScheme R n d).homOfLE inf_le_right ≫
          (selectedUniversalOpenIso R n d b).inv = selectedChartOverlapMap R a b := by
  rw [← Category.assoc, selectedUniversalOverlapIso_second]
  simp

end FlagVarieties.Foundations.QuotientCharts
