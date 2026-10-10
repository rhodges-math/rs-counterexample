import RSCounterexample.FlagVarieties.Foundations.Schemes.AffineCoordinateSheafRecovery

/-!
# Source-preserving sheaf isomorphisms determine the original coordinate kernel

The affine coordinate kernel is invariant under an isomorphism of quotient
targets that preserves the labelled quotient map. Thus the sheaf
comparison identifies the original Grassmannian point, not only a module
isomorphism class.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u
variable (A : CommRingCat.{u}) {n : ℕ} {M N : (Spec A).Modules}

theorem affineCoordinateQuotientMap_comp
    (q : coordinateFreeSheaf (Spec A) n ⟶ M) (f : M ⟶ N) :
    ModuleCat.ofHom (affineCoordinateQuotientMap A (q ≫ f)) =
      ModuleCat.ofHom (affineCoordinateQuotientMap A q) ≫ moduleSpecΓFunctor.map f := by
  change (coordinateFreeGlobalIso A n).hom ≫ moduleSpecΓFunctor.map (q ≫ f) =
    ((coordinateFreeGlobalIso A n).hom ≫ moduleSpecΓFunctor.map q) ≫ moduleSpecΓFunctor.map f
  rw [Functor.map_comp, Category.assoc]

theorem affineCoordinateQuotientMap_ker_iso
    (q : coordinateFreeSheaf (Spec A) n ⟶ M)
    (r : coordinateFreeSheaf (Spec A) n ⟶ N) (e : M ≅ N) (he : q ≫ e.hom = r) :
    LinearMap.ker (affineCoordinateQuotientMap A q) =
      LinearMap.ker (affineCoordinateQuotientMap A r) := by
  subst r
  have hi : Function.Injective (moduleSpecΓFunctor.map e.hom) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  apply Submodule.ext
  intro x
  change affineCoordinateQuotientMap A q x = 0 ↔
    affineCoordinateQuotientMap A (q ≫ e.hom) x = 0
  have hm := congrArg (fun f => f.hom x) (affineCoordinateQuotientMap_comp A q e.hom)
  change affineCoordinateQuotientMap A (q ≫ e.hom) x =
    (moduleSpecΓFunctor.map e.hom).hom (affineCoordinateQuotientMap A q x) at hm
  rw [hm]
  change affineCoordinateQuotientMap A q x = 0 ↔
    (moduleSpecΓFunctor.map e.hom).hom (affineCoordinateQuotientMap A q x) = 0
  rw [← map_zero (moduleSpecΓFunctor.map e.hom).hom]
  exact hi.eq_iff.symm

/-- A source-preserving sheaf isomorphism identifies coordinate quotients literally. -/
theorem coordinateQuotient_eq_of_sheaf_iso {d : ℕ}
    (P Q : Module.Grassmannian A (Fin n → A) d)
    (e : coordinateQuotientSheaf A P ≅ coordinateQuotientSheaf A Q)
    (he : coordinateQuotientSheafMap A P ≫ e.hom = coordinateQuotientSheafMap A Q) :
    P = Q := by
  apply Module.Grassmannian.ext
  rw [← affineCoordinateQuotientMap_ker_of_coordinate A P,
    ← affineCoordinateQuotientMap_ker_of_coordinate A Q]
  exact affineCoordinateQuotientMap_ker_iso A _ _ e he

end FlagVarieties.Foundations.QuotientCharts
