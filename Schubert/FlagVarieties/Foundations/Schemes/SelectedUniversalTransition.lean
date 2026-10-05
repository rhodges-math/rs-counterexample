import Schubert.FlagVarieties.Foundations.Schemes.SelectedUniversalLocalRestriction

/-!
# Target transitions on the full universal chart intersections

The original quotient points agree on the determinant localization.
Their canonical sheaf target isomorphism transports to the full intersection
and preserves the restriction of the one original global free source.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : Type u) [CommRing R] {n d : ℕ} (a b : Fin d ↪ Fin n)

/-- The two affine presentations on the determinant overlap define
exactly the same quotient of the original ambient module. -/
theorem selectedUniversalAffinePoint_eq :
    selectedChartPoint R a
      (IsScalarTower.toAlgHom R (MvPolynomial (Fin d × Fin (n - d)) R)
        (Localization.Away (selectedPolynomialBlock R a b).det)) =
    selectedChartPoint R b
      (matrixOverlapCoordinates R (selectedPolynomialBlock R a b)
        (remainingPolynomialBlock R a b)) := by
  have h := selectedChartPoint_transition R a b
    (IsScalarTower.toAlgHom R (MvPolynomial (Fin d × Fin (n - d)) R)
      (Localization.Away (selectedPolynomialBlock R a b).det))
    (IsLocalization.Away.algebraMap_isUnit (selectedPolynomialBlock R a b).det)
  rw [selectedChartTransitionHom_algebraMap] at h
  exact h

/-- Free-target isomorphism on the determinant overlap. -/
def selectedUniversalAffineTransition :
    coordinateFreeSheaf
      (Spec (CommRingCat.of (Localization.Away (selectedPolynomialBlock R a b).det))) d ≅
    coordinateFreeSheaf
      (Spec (CommRingCat.of (Localization.Away (selectedPolynomialBlock R a b).det))) d :=
  selectedPresentationSheafTransition R
    (CommRingCat.of (Localization.Away (selectedPolynomialBlock R a b).det)) a b
    (IsScalarTower.toAlgHom R (MvPolynomial (Fin d × Fin (n - d)) R)
      (Localization.Away (selectedPolynomialBlock R a b).det))
    (matrixOverlapCoordinates R (selectedPolynomialBlock R a b) (remainingPolynomialBlock R a b))
    (selectedUniversalAffinePoint_eq R a b)

/-- The free-target transition on the full intersection open subscheme. -/
def selectedUniversalNormalizedTransition :
    coordinateFreeSheaf (selectedUniversalOpen R n d a ⊓ selectedUniversalOpen R n d b).toScheme d ≅
    coordinateFreeSheaf
      (selectedUniversalOpen R n d a ⊓ selectedUniversalOpen R n d b).toScheme d :=
  coordinateRestrictIso (selectedUniversalOverlapIso R a b).inv
    (selectedUniversalAffineTransition R a b)

/-- No intersection-coordinate compatibility is assumed: it follows by
transporting the source-preserving affine transition. -/
@[reassoc]
theorem selectedUniversalNormalizedTransition_comp :
    coordinateRestrictMap ((selectedChartScheme R n d).homOfLE
      (inf_le_left : selectedUniversalOpen R n d a ⊓ selectedUniversalOpen R n d b ≤ _))
      (selectedUniversalNormalizedQuotient R a) ≫
        (selectedUniversalNormalizedTransition R a b).hom =
    coordinateRestrictMap ((selectedChartScheme R n d).homOfLE
      (inf_le_right : selectedUniversalOpen R n d a ⊓ selectedUniversalOpen R n d b ≤ _))
      (selectedUniversalNormalizedQuotient R b) := by
  apply (coordinateRestrictMap_injective (selectedUniversalOverlapIso R a b).hom)
  rw [coordinateRestrictMap_comp, selectedUniversalNormalizedQuotient_first,
    selectedUniversalNormalizedQuotient_second]
  have ht : coordinateRestrictMap (selectedUniversalOverlapIso R a b).hom
      (selectedUniversalNormalizedTransition R a b).hom =
      (selectedUniversalAffineTransition R a b).hom := by
    change coordinateRestrictMap (selectedUniversalOverlapIso R a b).hom
      (coordinateRestrictMap (selectedUniversalOverlapIso R a b).inv _) = _
    rw [coordinateRestrictMap_comp_scheme]
    simp only [Iso.hom_inv_id, coordinateRestrictMap_id]
  rw [ht]
  exact selectedPresentationSheafTransition_comp R _ a b _ _ _

/-- Target transition between the restrictions of the two original
local target sheaves. -/
def selectedUniversalTargetTransition :
    (selectedUniversalLocalTarget R n d a).restrict
      ((selectedChartScheme R n d).homOfLE
        (inf_le_left : selectedUniversalOpen R n d a ⊓ selectedUniversalOpen R n d b ≤ _)) ≅
    (selectedUniversalLocalTarget R n d b).restrict
      ((selectedChartScheme R n d).homOfLE
        (inf_le_right : selectedUniversalOpen R n d a ⊓ selectedUniversalOpen R n d b ≤ _)) :=
  coordinateRestrictFreeIso ((selectedChartScheme R n d).homOfLE inf_le_left) d ≪≫
    selectedUniversalNormalizedTransition R a b ≪≫
    (coordinateRestrictFreeIso ((selectedChartScheme R n d).homOfLE inf_le_right) d).symm

/-- The full-intersection transition preserves the restrictions of the
original local quotients, with the canonical common-source identification. -/
@[reassoc]
theorem selectedUniversalTargetTransition_comp :
    (ModuleSheafGluing.restrictionThroughChart
      (inf_le_left : selectedUniversalOpen R n d a ⊓ selectedUniversalOpen R n d b ≤ _)).hom.app
        (coordinateFreeSheaf (selectedChartScheme R n d) n) ≫
      (Scheme.Modules.restrictFunctor ((selectedChartScheme R n d).homOfLE inf_le_left)).map
        (selectedUniversalLocalQuotient R n d a) ≫
          (selectedUniversalTargetTransition R a b).hom =
    (ModuleSheafGluing.restrictionThroughChart
      (inf_le_right : selectedUniversalOpen R n d a ⊓ selectedUniversalOpen R n d b ≤ _)).hom.app
        (coordinateFreeSheaf (selectedChartScheme R n d) n) ≫
      (Scheme.Modules.restrictFunctor ((selectedChartScheme R n d).homOfLE inf_le_right)).map
        (selectedUniversalLocalQuotient R n d b) := by
  apply (cancel_mono (coordinateRestrictFreeIso
    ((selectedChartScheme R n d).homOfLE
      (inf_le_right : selectedUniversalOpen R n d a ⊓ selectedUniversalOpen R n d b ≤ _)) d).hom).mp
  simp only [selectedUniversalTargetTransition, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [selectedUniversalLocalQuotient_eq, selectedUniversalLocalQuotient_eq,
    coordinateRestrictMap_through_assoc, coordinateRestrictMap_through]
  rw [selectedUniversalNormalizedTransition_comp]

end FlagVarieties.Foundations.QuotientCharts
