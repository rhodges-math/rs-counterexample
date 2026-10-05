import Schubert.FlagVarieties.Foundations.Schemes.AffineCoordinateSheafPresentation

/-!
# Recovery of the original coordinate kernel from its associated quotient

The affine sheaf-to-module construction agrees with the original module
quotient map through the canonical tilde unit. Consequently it returns
the identical ambient kernel, not merely an abstract isomorphic quotient.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u
variable (A : CommRingCat.{u}) {n d : ℕ}
  (P : Module.Grassmannian A (Fin n → A) d)

theorem affineCoordinateQuotientMap_of_coordinate :
    ModuleCat.ofHom (affineCoordinateQuotientMap A (coordinateQuotientSheafMap A P)) =
      ModuleCat.ofHom P.toSubmodule.mkQ ≫
        (tilde.adjunction (R := A)).unit.app
          (ModuleCat.of A ((Fin n → A) ⧸ P.toSubmodule)) := by
  change ((tilde.adjunction (R := A)).unit.app (ModuleCat.of A (Fin n → A)) ≫
    moduleSpecΓFunctor.map (coordinateTildeFreeIso A n).hom) ≫
    moduleSpecΓFunctor.map
      ((coordinateTildeFreeIso A n).inv ≫ tilde.map (ModuleCat.ofHom P.toSubmodule.mkQ)) = _
  rw [Functor.map_comp, Category.assoc,
    ← Category.assoc (moduleSpecΓFunctor.map (coordinateTildeFreeIso A n).hom),
    ← Functor.map_comp, Iso.hom_inv_id]
  rw [(moduleSpecΓFunctor (R := A)).map_id (tilde (ModuleCat.of A (Fin n → A))),
    Category.id_comp]
  exact ((tilde.adjunction (R := A)).unit.naturality (ModuleCat.ofHom P.toSubmodule.mkQ)).symm

/-- The original Grassmannian submodule is recovered literally. -/
theorem affineCoordinateQuotientMap_ker_of_coordinate :
    LinearMap.ker (affineCoordinateQuotientMap A (coordinateQuotientSheafMap A P)) =
      P.toSubmodule := by
  let η := (tilde.adjunction (R := A)).unit.app
    (ModuleCat.of A ((Fin n → A) ⧸ P.toSubmodule))
  have hη : Function.Injective η := (ModuleCat.mono_iff_injective η).mp inferInstance
  rw [← Submodule.ker_mkQ P.toSubmodule]
  apply Submodule.ext
  intro x
  change affineCoordinateQuotientMap A (coordinateQuotientSheafMap A P) x = 0 ↔
    P.toSubmodule.mkQ x = 0
  have he : affineCoordinateQuotientMap A (coordinateQuotientSheafMap A P) x =
      η (P.toSubmodule.mkQ x) :=
    congrArg (fun f => f.hom x) (affineCoordinateQuotientMap_of_coordinate A P)
  rw [he]
  change η.hom (P.toSubmodule.mkQ x) = 0 ↔ P.toSubmodule.mkQ x = 0
  rw [← map_zero η.hom]
  exact hη.eq_iff

end FlagVarieties.Foundations.QuotientCharts
