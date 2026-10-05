import Schubert.FlagVarieties.Foundations.Schemes.AffineCoordinateQuotientBaseChangeNormalization

/-!
# Labelled coordinate source of the affine quotient base-change comparison

The associated quotient sheaf comparison is compatible with the source
normalization used by the universal quotient's pullback map.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory

universe u

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
  {n d : ℕ} (P : Module.Grassmannian R (Fin n → R) d)

private theorem coordinateTildeFreePullbackIso_normalized_inv :
    (coordinatePullbackFreeIso
      (Spec.map (CommRingCat.ofHom (algebraMap R B))) n).inv ≫
      (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))).map
          (coordinateTildeFreeIso (CommRingCat.of R) n).inv ≫
        (coordinateTildeFreePullbackIso R B (n := n)).hom =
    (coordinateTildeFreeIso (CommRingCat.of B) n).inv := by
  have hIso :
      (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))).mapIso
          (coordinateTildeFreeIso (CommRingCat.of R) n) ≪≫
        coordinatePullbackFreeIso
          (Spec.map (CommRingCat.ofHom (algebraMap R B))) n =
      coordinateTildeFreePullbackIso R B (n := n) ≪≫
        coordinateTildeFreeIso (CommRingCat.of B) n := by
    apply Iso.ext
    simpa only [Iso.trans_hom, Functor.mapIso_hom] using
      coordinateTildeFreePullbackIso_normalized R B (n := n)
  have hInv := congrArg (fun t => t.inv) hIso
  simp only [Iso.trans_inv, Functor.mapIso_inv] at hInv
  have hh := congrArg (fun t => t ≫
      (coordinateTildeFreePullbackIso R B (n := n)).hom) hInv
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hh

/-- The affine sheaf quotient base-change isomorphism preserves the
original normalized labelled coordinate source. -/
theorem coordinateQuotientSheafPullbackIso_coordinate_source :
    coordinatePullbackQuotient
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (coordinateQuotientSheafMap (CommRingCat.of R) P) ≫
      (coordinateQuotientSheafPullbackIso R B P).hom =
    coordinateQuotientSheafMap (CommRingCat.of B)
      (coordinateGrassmannianBaseChange B P) := by
  simp only [coordinatePullbackQuotient, coordinateQuotientSheafMap,
    Functor.map_comp, Category.assoc]
  rw [← Category.assoc, coordinateQuotientSheafPullbackIso_source]
  simp only [Category.assoc]
  have h := congrArg (fun t => t ≫ tilde.map (ModuleCat.ofHom
      (coordinateGrassmannianBaseChange B P).toSubmodule.mkQ))
    (coordinateTildeFreePullbackIso_normalized_inv R B (n := n))
  simpa only [Category.assoc] using h

end FlagVarieties.Foundations.QuotientCharts
