import RSCounterexample.FlagVarieties.Foundations.Schemes.AffineCoordinateQuotientBaseChangeSheaf

/-!
# The original quotient source under affine sheaf pullback

The comparison of associated quotient sheaves is paired with the
corresponding comparison of the ambient coordinate module sheaves. Their
square preserves the original quotient map `P.toSubmodule.mkQ`.
The further identification with the canonical labelled free-sheaf pullback
isomorphism is `Schemes/AffineCoordinateQuotientBaseChangeNormalization.lean`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory

universe u

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
  {n d : ℕ} (P : Module.Grassmannian R (Fin n → R) d)

/-- Associated-sheaf pullback comparison on the original ambient
finite-coordinate module. -/
def coordinateTildeFreePullbackIso :
    (Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))).obj
        (tilde (ModuleCat.of R (Fin n → R))) ≅
      tilde (ModuleCat.of B (Fin n → B)) :=
  AffineTildePullback.baseChangeIso (CommRingCat.ofHom (algebraMap R B))
      (ModuleCat.of R (Fin n → R)) ≪≫
    (tilde.functor (CommRingCat.of B)).mapIso
      (coordinateExtendedFreeIso R B (n := n))

/-- The sheaf quotient square retains the original ambient quotient
map under arbitrary scalar extension. -/
theorem coordinateQuotientSheafPullbackIso_source :
    (Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))).map
        (tilde.map (ModuleCat.ofHom P.toSubmodule.mkQ)) ≫
      (coordinateQuotientSheafPullbackIso R B P).hom =
    (coordinateTildeFreePullbackIso R B (n := n)).hom ≫
      tilde.map (ModuleCat.ofHom
        (coordinateGrassmannianBaseChange B P).toSubmodule.mkQ) := by
  simp only [coordinateQuotientSheafPullbackIso, coordinateTildeFreePullbackIso,
    Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap R B)))).map
      (tilde.map (ModuleCat.ofHom P.toSubmodule.mkQ))),
    AffineTildePullback.baseChangeIso_map]
  simp only [Category.assoc]
  have h := congrArg (tilde.functor (CommRingCat.of B)).map
    (coordinateExtendedQuotientIso_source R B P)
  simp only [Functor.map_comp] at h
  simpa only [AffineTildePullback.specMap, coordinateQuotientSheaf,
    tilde.functor, CommRingCat.hom_ofHom, Category.assoc] using congrArg
    (fun t => (AffineTildePullback.baseChangeIso
      (CommRingCat.ofHom (algebraMap R B))
      (ModuleCat.of R (Fin n → R))).hom ≫ t) h

end FlagVarieties.Foundations.QuotientCharts
