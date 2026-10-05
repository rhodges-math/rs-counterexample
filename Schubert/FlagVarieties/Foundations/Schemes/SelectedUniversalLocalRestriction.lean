import Schubert.FlagVarieties.Foundations.Schemes.SelectedUniversalRestrictionTransport
import Schubert.FlagVarieties.Foundations.Schemes.SelectedUniversalOverlap

/-!
# Original quotient formulas on chart intersections

Canonical free-sheaf comparisons identify restriction of each original local
quotient with its affine base change on the determinant localization.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- Restricting a quotient of the one global free source retains its original
source identification through the containing chart. -/
@[reassoc]
theorem coordinateRestrictMap_through {X : Scheme.{u}} {V W : X.Opens}
    (h : W ≤ V) {n d : ℕ}
    (q : coordinateFreeSheaf V.toScheme n ⟶ coordinateFreeSheaf V.toScheme d) :
    (ModuleSheafGluing.restrictionThroughChart h).hom.app (coordinateFreeSheaf X n) ≫
      (Scheme.Modules.restrictFunctor (X.homOfLE h)).map
        ((coordinateRestrictFreeIso V.ι n).hom ≫ q) ≫
      (coordinateRestrictFreeIso (X.homOfLE h) d).hom =
    (coordinateRestrictFreeIso W.ι n).hom ≫ coordinateRestrictMap (X.homOfLE h) q := by
  rw [← coordinateRestrictFreeIso_through h n]
  simp only [coordinateRestrictMap, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

variable (R : Type u) [CommRing R] {n d : ℕ}

/-- The identity-evaluated affine quotient transported to the range open. -/
def selectedUniversalNormalizedQuotient (a : Fin d ↪ Fin n) :
    coordinateFreeSheaf (selectedUniversalOpen R n d a).toScheme n ⟶
      coordinateFreeSheaf (selectedUniversalOpen R n d a).toScheme d :=
  coordinateRestrictMap (selectedUniversalOpenIso R n d a).inv
    (selectedPresentationSheafMap R
      (CommRingCat.of (MvPolynomial (Fin d × Fin (n - d)) R)) a (AlgHom.id R _))

/-- This is the original local quotient, with only its source frame factored out. -/
theorem selectedUniversalLocalQuotient_eq (a : Fin d ↪ Fin n) :
    selectedUniversalLocalQuotient R n d a =
      (coordinateRestrictFreeIso (selectedUniversalOpen R n d a).ι n).hom ≫
        selectedUniversalNormalizedQuotient R a := by
  unfold selectedUniversalNormalizedQuotient
  rw [coordinateRestrictMap_eq_pullback]
  rfl

/-- The first original quotient on the full intersection, seen through the
determinant-overlap isomorphism, is exactly scalar extension. -/
theorem selectedUniversalNormalizedQuotient_first (a b : Fin d ↪ Fin n) :
    coordinateRestrictMap (selectedUniversalOverlapIso R a b).hom
      (coordinateRestrictMap ((selectedChartScheme R n d).homOfLE
        (inf_le_left : selectedUniversalOpen R n d a ⊓ selectedUniversalOpen R n d b ≤ _))
          (selectedUniversalNormalizedQuotient R a)) =
    selectedPresentationSheafMap R
      (CommRingCat.of (Localization.Away (selectedPolynomialBlock R a b).det)) a
      (IsScalarTower.toAlgHom R (MvPolynomial (Fin d × Fin (n - d)) R)
        (Localization.Away (selectedPolynomialBlock R a b).det)) := by
  unfold selectedUniversalNormalizedQuotient
  rw [coordinateRestrictMap_comp_scheme, coordinateRestrictMap_comp_scheme]
  simp only [Category.assoc, selectedUniversalOverlapIso_first_chart]
  rw [coordinateRestrictMap_eq_pullback]
  change (coordinatePullbackIso _ n).inv ≫ _ ≫ (coordinatePullbackIso _ d).hom = _
  simpa only [AlgHom.comp_id, selectedChartOverlapInclusion, selectedChartOverlapMap,
    matrixOverlapMap, IsScalarTower.toAlgHom] using
    selectedPresentationSheafMap_pullback_conjugate R
    (CommRingCat.of (MvPolynomial (Fin d × Fin (n - d)) R))
    (CommRingCat.of (Localization.Away (selectedPolynomialBlock R a b).det)) a
    (AlgHom.id R _)
    (IsScalarTower.toAlgHom R (MvPolynomial (Fin d × Fin (n - d)) R)
      (Localization.Away (selectedPolynomialBlock R a b).det))

/-- The second original quotient becomes the regular overlap coordinates. -/
theorem selectedUniversalNormalizedQuotient_second (a b : Fin d ↪ Fin n) :
    coordinateRestrictMap (selectedUniversalOverlapIso R a b).hom
      (coordinateRestrictMap ((selectedChartScheme R n d).homOfLE
        (inf_le_right : selectedUniversalOpen R n d a ⊓ selectedUniversalOpen R n d b ≤ _))
          (selectedUniversalNormalizedQuotient R b)) =
    selectedPresentationSheafMap R
      (CommRingCat.of (Localization.Away (selectedPolynomialBlock R a b).det)) b
      (matrixOverlapCoordinates R (selectedPolynomialBlock R a b)
        (remainingPolynomialBlock R a b)) := by
  unfold selectedUniversalNormalizedQuotient
  rw [coordinateRestrictMap_comp_scheme, coordinateRestrictMap_comp_scheme]
  simp only [Category.assoc, selectedUniversalOverlapIso_second_chart]
  rw [coordinateRestrictMap_eq_pullback]
  change (coordinatePullbackIso _ n).inv ≫ _ ≫ (coordinatePullbackIso _ d).hom = _
  simpa only [AlgHom.comp_id, selectedChartOverlapInclusion, selectedChartOverlapMap,
    matrixOverlapMap, IsScalarTower.toAlgHom] using
    selectedPresentationSheafMap_pullback_conjugate R
    (CommRingCat.of (MvPolynomial (Fin d × Fin (n - d)) R))
    (CommRingCat.of (Localization.Away (selectedPolynomialBlock R a b).det)) b
    (AlgHom.id R _)
    (matrixOverlapCoordinates R (selectedPolynomialBlock R a b) (remainingPolynomialBlock R a b))

end FlagVarieties.Foundations.QuotientCharts
