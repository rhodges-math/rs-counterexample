import RSCounterexample.FlagVarieties.Foundations.Schemes.AffineTildeTensor
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# The two adjunctions behind affine associated-sheaf base change

The sheaf pullback and module scalar extension each follow the
associated-sheaf functor. Their right adjoints are global sections after
pushforward and global sections with scalar restriction, respectively.
The explicit scalar-action comparison identifies those right adjoints;
uniqueness of left adjoints then gives the sheaf pullback isomorphism.
-/

noncomputable section

namespace FlagVarieties.Foundations.AffineTildePullback

open AlgebraicGeometry CategoryTheory

universe u

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- The affine scheme map induced by the coefficient homomorphism. -/
abbrev specMap : Spec S ⟶ Spec R := Spec.map φ

/-- Pullback after `tilde` is left adjoint to pushforward followed by sections. -/
def sheafAdjunction :
    (tilde.functor R ⋙ Scheme.Modules.pullback (specMap φ)) ⊣
      (Scheme.Modules.pushforward (specMap φ) ⋙ moduleSpecΓFunctor (R := R)) :=
  (tilde.adjunction (R := R)).comp (Scheme.Modules.pullbackPushforwardAdjunction (specMap φ))

/-- Scalar extension followed by `tilde` is left adjoint to sections followed by restriction. -/
def moduleAdjunction :
    (ModuleCat.extendScalars φ.hom ⋙ tilde.functor S) ⊣
      (moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom) :=
  (ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S))

/-- The affine top-section coefficient maps commute with the scheme map. -/
theorem specMap_appTop_coefficient (r : R) :
    (specMap φ).appTop.hom ((Scheme.ΓSpecIso R).inv r) =
      (Scheme.ΓSpecIso S).inv (φ.hom r) := by
  exact congrArg (fun h : R ⟶ Γ(Spec S, ⊤) => h.hom r)
    (Scheme.ΓSpecIso_inv_naturality φ).symm

/-- At the level of underlying types, top sections after pushforward are top sections. -/
theorem pushforward_top_sections_type (M : (Spec S).Modules) :
    Γ((Scheme.Modules.pushforward (specMap φ)).obj M, ⊤) = Γ(M, ⊤) := by
  rfl

/-- On a fixed sheaf, affine pushforward global sections are scalar restriction. -/
def rightObjectIso (M : (Spec S).Modules) :
    (Scheme.Modules.pushforward (specMap φ) ⋙ moduleSpecΓFunctor (R := R)).obj M ≅
      (moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom).obj M := by
  letI : Module Γ(Spec S, ⊤)
      ((Scheme.Modules.pushforward (specMap φ) ⋙ moduleSpecΓFunctor (R := R)).obj M) :=
    show Module Γ(Spec S, ⊤) Γ(M, ⊤) from inferInstance
  let e :
      ((Scheme.Modules.pushforward (specMap φ) ⋙ moduleSpecΓFunctor (R := R)).obj M) ≃ₗ[R]
        ((moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom).obj M) := {
    toFun := id
    invFun := id
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := by intros; rfl
    map_smul' := by
      intro r x
      change (specMap φ).appTop.hom ((Scheme.ΓSpecIso R).inv r) •
          (x : Γ(M, ⊤)) =
        (Scheme.ΓSpecIso S).inv (φ.hom r) • (x : Γ(M, ⊤))
      rw [specMap_appTop_coefficient φ r]
  }
  exact e.toModuleIso

/-- The top-section scalar comparison is natural in the sheaf. -/
def rightAdjunctionIso :
    (Scheme.Modules.pushforward (specMap φ) ⋙ moduleSpecΓFunctor (R := R)) ≅
      (moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom) :=
  NatIso.ofComponents (fun M => rightObjectIso φ M) (by
    intro M N f
    apply ModuleCat.hom_ext
    rfl)

/-- Sheaf pullback of an associated sheaf equals the associated sheaf
of module scalar extension for every affine coefficient homomorphism. -/
def baseChangeNatIso :
    (tilde.functor R ⋙ Scheme.Modules.pullback (specMap φ)) ≅
      (ModuleCat.extendScalars φ.hom ⋙ tilde.functor S) :=
  Adjunction.leftAdjointUniq (sheafAdjunction φ)
    ((moduleAdjunction φ).ofNatIsoRight (rightAdjunctionIso φ).symm)

end FlagVarieties.Foundations.AffineTildePullback
