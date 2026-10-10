import RSCounterexample.FlagVarieties.Foundations.Schemes.AffineTildePullbackAdjunction

/-!
# Source compatibility of affine associated-sheaf pullback

The affine base-change isomorphism is natural for every module morphism.
In particular it carries the sheaf map of an original module quotient
to the associated sheaf map of its tensor-extended quotient morphism.
-/

noncomputable section

namespace FlagVarieties.Foundations.AffineTildePullback

open AlgebraicGeometry CategoryTheory

universe u

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- The objectwise associated-sheaf pullback comparison. -/
def baseChangeIso (M : ModuleCat.{u} R) :
    (Scheme.Modules.pullback (specMap φ)).obj (tilde M) ≅
      tilde ((ModuleCat.extendScalars φ.hom).obj M) :=
  (baseChangeNatIso φ).app M

/-- The comparison carries every original sheaf morphism to its module scalar extension. -/
@[reassoc]
theorem baseChangeIso_map {M N : ModuleCat.{u} R} (q : M ⟶ N) :
    (Scheme.Modules.pullback (specMap φ)).map (tilde.map q) ≫
      (baseChangeIso φ N).hom =
    (baseChangeIso φ M).hom ≫
      tilde.map ((ModuleCat.extendScalars φ.hom).map q) :=
  (baseChangeNatIso φ).hom.naturality q

/-- Applying the sheaf pullback comparison to the original module quotient map. -/
@[reassoc]
theorem baseChangeIso_quotient_source (M : ModuleCat.{u} R) (K : Submodule R M) :
    (Scheme.Modules.pullback (specMap φ)).map
        (tilde.map (ModuleCat.ofHom K.mkQ)) ≫
      (baseChangeIso φ (ModuleCat.of R (M ⧸ K))).hom =
    (baseChangeIso φ M).hom ≫
      tilde.map ((ModuleCat.extendScalars φ.hom).map (ModuleCat.ofHom K.mkQ)) :=
  baseChangeIso_map φ (ModuleCat.ofHom K.mkQ)

end FlagVarieties.Foundations.AffineTildePullback
