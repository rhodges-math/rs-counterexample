import Schubert.FlagVarieties.Foundations.Schemes.AffineTildeFrames
import Schubert.FlagVarieties.Foundations.Schemes.QuotientPairScheme

/-!
# Open-scheme tensor modules and associated-sheaf sections

The coefficient ring used by `ModuleOn` is the global-section ring of the
open subscheme. Its comparison with sections on the corresponding open is
the `Scheme.Opens.topIso`, not a definitional identification.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientPair

open AlgebraicGeometry CategoryTheory TensorProduct

universe u

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (f : R)

/-- The basic open set `D(f) ⊆ Spec R`. -/
abbrev principalOpen : (Spec R).Opens := PrimeSpectrum.basicOpen f

attribute [local instance] openAlgebra

/-- The base coefficient map factors through the affine global-section ring. -/
@[instance_reducible] def principalOpenAlgebra : Algebra R (RingOn (principalOpen f)) :=
  ((algebraMap Γ(Spec R, ⊤) (RingOn (principalOpen f))).comp
    (algebraMap R Γ(Spec R, ⊤))).toAlgebra

attribute [local instance] principalOpenAlgebra

theorem principal_topIso_algebraMap (r : R) :
    (principalOpen f).topIso.hom (algebraMap R (RingOn (principalOpen f)) r) =
      algebraMap R (PrincipalRing f) r := by
  change ((principalOpen f).ι.appTop ≫ (principalOpen f).topIso.hom)
    ((Scheme.ΓSpecIso R).inv r) = _
  have h : (principalOpen f).ι.appTop ≫ (principalOpen f).topIso.hom =
      (Spec R).presheaf.map (homOfLE (show principalOpen f ≤ ⊤ from le_top)).op := by
    simp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← Functor.map_comp]
    rfl
  rw [h]
  rfl

/-- The top-open ring comparison respects the base coefficient homomorphism. -/
def principalTopAlgEquiv : RingOn (principalOpen f) ≃ₐ[R] PrincipalRing f where
  __ := (principalOpen f).topIso.commRingCatIsoToRingEquiv
  commutes' := principal_topIso_algebraMap f

instance principalOpenLocalization : IsLocalization.Away f (RingOn (principalOpen f)) :=
  IsLocalization.isLocalization_of_algEquiv (Submonoid.powers f)
    (principalTopAlgEquiv f).symm

/-- Sections viewed over the global-section ring of the open subscheme. -/
@[instance_reducible] def principalOpenSectionModule :
    Module (RingOn (principalOpen f)) (PrincipalSections M f) :=
  Module.compHom (PrincipalSections M f) (principalOpen f).topIso.hom.hom

attribute [local instance] principalOpenSectionModule

instance principalOpenSectionTower :
    IsScalarTower R (RingOn (principalOpen f)) (PrincipalSections M f) :=
  IsScalarTower.of_algebraMap_smul fun r m => by
    change (principalOpen f).topIso.hom (algebraMap R (RingOn (principalOpen f)) r) • m = r • m
    rw [principal_topIso_algebraMap, IsScalarTower.algebraMap_smul]

/-- Scalar extension over the open-scheme ring is the section module. -/
def principalOpenTensorEquiv :
    RingOn (principalOpen f) ⊗[R] M ≃ₗ[RingOn (principalOpen f)] PrincipalSections M f :=
  (IsLocalizedModule.isBaseChange (Submonoid.powers f) (RingOn (principalOpen f))
    (principalToSections M f)).equiv

@[simp] theorem principalOpenTensorEquiv_one_tmul (m : M) :
    principalOpenTensorEquiv M f (1 ⊗ₜ[R] m) = principalToSections M f m := by
  simp [principalOpenTensorEquiv, IsBaseChange.equiv_tmul]

instance principalOpenGlobalTower :
    IsScalarTower R Γ(Spec R, ⊤) (RingOn (principalOpen f)) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The global coefficient extension used as the input module of the existing gluing API. -/
abbrev AffineGlobalModule := Γ(Spec R, ⊤) ⊗[R] M

/-- Exact comparison for the earlier `ModuleOn` tensor module, including its global base ring. -/
def principalModuleOnEquiv :
    ModuleOn (Q := AffineGlobalModule M) (principalOpen f) ≃ₗ[RingOn (principalOpen f)]
      PrincipalSections M f :=
  AlgebraTensorModule.cancelBaseChange R Γ(Spec R, ⊤) (RingOn (principalOpen f))
    (RingOn (principalOpen f)) M ≪≫ₗ principalOpenTensorEquiv M f

@[simp] theorem principalModuleOnEquiv_one_tmul (m : M) :
    principalModuleOnEquiv M f (1 ⊗ₜ[Γ(Spec R, ⊤)] (1 ⊗ₜ[R] m)) =
      principalToSections M f m := by
  simp [principalModuleOnEquiv]

/-- A frame of sections gives a frame over the open-scheme ring. -/
def principalOpenFrame
    (frame : PrincipalSections M f ≃ₗ[PrincipalRing f] PrincipalRing f) :
    PrincipalSections M f ≃ₗ[RingOn (principalOpen f)] RingOn (principalOpen f) :=
  (frame.restrictScalars R ≪≫ₗ
      (principalTopAlgEquiv f).symm.toLinearEquiv).extendScalarsOfIsLocalization
    (Submonoid.powers f) (RingOn (principalOpen f))

/-- An associated-sheaf frame supplies the tensor-module frame used in gluing. -/
def principalModuleOnFrame
    (frame : PrincipalSections M f ≃ₗ[PrincipalRing f] PrincipalRing f) :
    ModuleOn (Q := AffineGlobalModule M) (principalOpen f) ≃ₗ[RingOn (principalOpen f)]
      RingOn (principalOpen f) :=
  principalModuleOnEquiv M f ≪≫ₗ principalOpenFrame M f frame

@[simp] theorem principalModuleOnFrame_one_tmul
    (frame : PrincipalSections M f ≃ₗ[PrincipalRing f] PrincipalRing f) (m : M) :
    principalModuleOnFrame M f frame (1 ⊗ₜ[Γ(Spec R, ⊤)] (1 ⊗ₜ[R] m)) =
      (principalOpen f).topIso.inv (frame (principalToSections M f m)) := by
  change principalOpenFrame M f frame
    (principalModuleOnEquiv M f (1 ⊗ₜ[Γ(Spec R, ⊤)] (1 ⊗ₜ[R] m))) = _
  rw [principalModuleOnEquiv_one_tmul]
  rfl

/-- The local frames required by the gluing API follow from finite projectivity and rank one. -/
theorem exists_principal_moduleOn_frame [Module.Finite R M] [Module.Projective R M]
    (p : PrimeSpectrum R) (hrank : Module.rankAtStalk M p = 1) :
    ∃ f : R, f ∉ p.asIdeal ∧
      Nonempty (ModuleOn (Q := AffineGlobalModule M) (principalOpen f) ≃ₗ[RingOn (principalOpen f)]
        RingOn (principalOpen f)) := by
  obtain ⟨f, hf, ⟨frame⟩⟩ := exists_principal_section_frame M p hrank
  exact ⟨f, hf, ⟨principalModuleOnFrame M f frame⟩⟩

end FlagVarieties.Foundations.QuotientPair

