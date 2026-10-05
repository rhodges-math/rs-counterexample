import Schubert.FlagVarieties.Foundations.Schemes.SelectedSheafRestriction
import Schubert.FlagVarieties.Foundations.Schemes.SelectedUniversalChart

/-!
# Agreement of the canonical restriction comparisons

The restriction comparison obtained through pullback agrees with the
standard restriction-unit comparison and hence with the canonical coproduct
comparison used for the local universal quotient on selected chart ranges.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

/-- The standard restriction unit is adjoint to the map of structure sheaves. -/
theorem restrictUnitIso_adjoint :
    ((Scheme.Modules.restrictAdjunction f).homEquiv _ _)
        (Scheme.Modules.restrictUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  rw [Adjunction.homEquiv_apply]
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change (f.appIso (f ⁻¹ᵁ U)).hom
      (X.presheaf.map (homOfLE (f.image_preimage_le U)).op x) = f.app U x
  have h : X.presheaf.map (homOfLE (f.image_preimage_le U)).op ≫
      (f.appIso (f ⁻¹ᵁ U)).hom = f.app U := by
    have hh : f.app U ≫ (f.appIso (f ⁻¹ᵁ U)).inv =
        X.presheaf.map (homOfLE (f.image_preimage_le U)).op := f.app_appIso_inv U
    rw [← hh, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact ConcreteCategory.congr_hom h x

/-- The pullback-derived unit comparison equals the standard restriction
comparison, by uniqueness of adjoints and the structure-sheaf map. -/
theorem coordinateRestrictionUnitIso_eq :
    coordinateRestrictionUnitIso f = Scheme.Modules.restrictUnitIso f := by
  apply Iso.ext
  apply ((Scheme.Modules.restrictAdjunction f).homEquiv _ _).injective
  rw [restrictUnitIso_adjoint]
  change ((Scheme.Modules.restrictAdjunction f).homEquiv _ _)
    (((Scheme.Modules.restrictAdjunction f).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction f)).hom.app (QuotientPair.unitSheaf X) ≫
        (QuotientPair.quotientPullbackUnitIso f).hom) = _
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app]
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    f.toRingCatSheafHom

/-- The restriction/pullback comparison is precisely the canonical free-sheaf
restriction comparison used by `selectedUniversalLocalQuotient`. -/
theorem coordinateRestrictionIso_eq (n : ℕ) :
    coordinateRestrictionIso f n = coordinateRestrictFreeIso f n := by
  have : PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor f) := inferInstance
  apply Iso.ext
  apply Cofan.IsColimit.hom_ext
    (isColimitCofanMkObjOfIsColimit (Scheme.Modules.restrictFunctor f) _ _
      (SheafOfModules.isColimitFreeCofan
        (R := X.ringCatSheaf) (CoordinateIndex.{u} n)))
  intro i
  change (Scheme.Modules.restrictFunctor f).map (SheafOfModules.ιFree i) ≫
      (coordinateRestrictionIso f n).hom =
    (Scheme.Modules.restrictFunctor f).map (SheafOfModules.ιFree i) ≫
      (coordinateRestrictFreeIso f n).hom
  rw [coordinateRestrictionIso_generator, coordinateRestrictionUnitIso_eq]
  exact (SheafOfModules.map_ιFree_mapFreeIso_inv (Scheme.Modules.restrictFunctor f)
    (CoordinateIndex.{u} n) (Scheme.Modules.restrictUnitIso f).symm i).symm

/-- Both affine-base-change and universal-chart pullback comparisons are the
same Mathlib labelled free-sheaf isomorphism. -/
theorem coordinatePullbackIso_eq {X Y : Scheme.{u}} (g : Y ⟶ X) (n : ℕ) :
    coordinatePullbackIso g n = coordinatePullbackFreeIso g n := rfl

end FlagVarieties.Foundations.QuotientCharts
