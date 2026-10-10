import RSCounterexample.FlagVarieties.Foundations.Schemes.ConstantMatrixSheaf
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedSheafBaseChangeCoordinates
import RSCounterexample.FlagVarieties.Foundations.Schemes.AffineCoordinateSheafUniqueness

/-! The constant-matrix automorphism of the affine free sheaf acts
on the original coordinate quotient by inverse change of source basis. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory

universe u
variable (A : CommRingCat.{u}) {n : ℕ} {M : (Spec A).Modules}

private theorem affineCoordinateQuotientMap_coordinate_precomp
    (T : (Fin n → A) →ₗ[A] (Fin n → A))
    (q : coordinateFreeSheaf (Spec A) n ⟶ M) :
    affineCoordinateQuotientMap A (coordinateSheafMap A T ≫ q) =
      (affineCoordinateQuotientMap A q).comp T := by
  have he : ModuleCat.ofHom (affineCoordinateQuotientMap A
        (coordinateSheafMap A T ≫ q)) =
      ModuleCat.ofHom T ≫ ModuleCat.ofHom (affineCoordinateQuotientMap A q) := by
    change (coordinateFreeGlobalIso A n).hom ≫
        moduleSpecΓFunctor.map (coordinateSheafMap A T ≫ q) =
      ModuleCat.ofHom T ≫ (coordinateFreeGlobalIso A n).hom ≫
        moduleSpecΓFunctor.map q
    simp only [coordinateFreeGlobalIso, coordinateSheafMap, Iso.trans_hom,
      asIso_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
    rw [← Category.assoc (moduleSpecΓFunctor.map
      (coordinateTildeFreeIso A n).hom),
      ← Functor.map_comp, Iso.hom_inv_id,
      (moduleSpecΓFunctor (R := A)).map_id, Category.id_comp]
    rw [← Category.assoc]
    have hnat :
        (tilde.adjunction (R := A)).unit.app (ModuleCat.of A (Fin n → A)) ≫
          moduleSpecΓFunctor.map (tilde.map (ModuleCat.ofHom T)) =
        ModuleCat.ofHom T ≫
          (tilde.adjunction (R := A)).unit.app (ModuleCat.of A (Fin n → A)) := by
      have hh := ((tilde.adjunction (R := A)).unit.naturality
        (ModuleCat.ofHom T)).symm
      change (tilde.adjunction (R := A)).unit.app (ModuleCat.of A (Fin n → A)) ≫
          moduleSpecΓFunctor.map (tilde.map (ModuleCat.ofHom T)) =
        ModuleCat.ofHom T ≫
          (tilde.adjunction (R := A)).unit.app (ModuleCat.of A (Fin n → A)) at hh
      exact hh
    rw [hnat]
    simp only [Category.assoc]
  have hh := congrArg ModuleCat.Hom.hom he
  change affineCoordinateQuotientMap A (coordinateSheafMap A T ≫ q) =
    (affineCoordinateQuotientMap A q).comp T at hh
  exact hh

variable (L : Matrix (Fin n) (Fin n) A) (hL : IsUnit L)

private theorem constantMatrixSpecIso_inv_eq_coordinateSheafMap :
    (constantMatrixSpecIso A L hL).inv = coordinateSheafMap A
      (L.toLinearEquiv' hL.invertible).symm.toLinearMap := by
  rfl

/-- The affine global-section quotient is precomposed with the
inverse of the original coordinate matrix action. -/
theorem affineCoordinateQuotientMap_constantMatrix_inv
    (q : coordinateFreeSheaf (Spec A) n ⟶ M) :
    affineCoordinateQuotientMap A ((constantMatrixSpecIso A L hL).inv ≫ q) =
      (affineCoordinateQuotientMap A q).comp
        (L.toLinearEquiv' hL.invertible).symm.toLinearMap := by
  rw [constantMatrixSpecIso_inv_eq_coordinateSheafMap]
  exact affineCoordinateQuotientMap_coordinate_precomp A _ q

/-- Consequently its original ambient coordinate kernel is the image of
the original kernel under the *forward* matrix action. -/
theorem affineCoordinateQuotientMap_constantMatrix_inv_ker
    (q : coordinateFreeSheaf (Spec A) n ⟶ M) :
    LinearMap.ker (affineCoordinateQuotientMap A
      ((constantMatrixSpecIso A L hL).inv ≫ q)) =
    Submodule.map (L.toLinearEquiv' hL.invertible).toLinearMap
      (LinearMap.ker (affineCoordinateQuotientMap A q)) := by
  rw [affineCoordinateQuotientMap_constantMatrix_inv]
  apply Submodule.ext
  intro x
  constructor
  · intro hx
    refine ⟨(L.toLinearEquiv' hL.invertible).symm x, hx, ?_⟩
    exact (L.toLinearEquiv' hL.invertible).apply_symm_apply x
  · rintro ⟨y, hy, rfl⟩
    change (affineCoordinateQuotientMap A q) y = 0 at hy
    change (affineCoordinateQuotientMap A q)
      ((L.toLinearEquiv' hL.invertible).symm
        ((L.toLinearEquiv' hL.invertible) y)) = 0
    simpa only [LinearEquiv.symm_apply_apply] using hy

end FlagVarieties.Foundations.QuotientCharts
