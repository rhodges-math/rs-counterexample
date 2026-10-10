import RSCounterexample.FlagVarieties.Foundations.Schemes.AffineTildeOpenTensor

/-!
# A projective morphism from an affine rank-one quotient

A surjective ordered pair into a finite projective rank-one module supplies
a morphism from `Spec R` to the two-variable Proj. The principal
cover and its frames are constructed from the associated sheaf.
No cover, frame, coprime coordinate pair, or overlap unit is an input.
This does not assert a universal property for arbitrary quotient sheaves.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientPair

open AlgebraicGeometry CategoryTheory TensorProduct TopologicalSpace

universe u

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

attribute [local instance] openAlgebra principalOpenAlgebra principalOpenSectionModule

/-- The coefficients in a section frame are coprime on the principal affine open. -/
theorem principal_section_coordinates_coprime (f : R)
    (q : R × R →ₗ[R] M) (hq : Function.Surjective q)
    (frame : PrincipalSections M f ≃ₗ[PrincipalRing f] PrincipalRing f) :
    IsCoprime (frame (principalToSections M f (q (1, 0))))
      (frame (principalToSections M f (q (0, 1)))) := by
  simpa only [LinearEquiv.trans_apply, principalTensorEquiv_one_tmul] using
    frame_coordinates_coprime q hq (principalTensorEquiv M f ≪≫ₗ frame)

/-- Scalar extension of the two ordered quotient generators to the affine global-section ring. -/
def affineGlobalPair (q : R × R →ₗ[R] M) :
    Γ(Spec R, ⊤) × Γ(Spec R, ⊤) →ₗ[Γ(Spec R, ⊤)] AffineGlobalModule M :=
  (LinearMap.fst _ _ _).smulRight (1 ⊗ₜ[R] q (1, 0)) +
    (LinearMap.snd _ _ _).smulRight (1 ⊗ₜ[R] q (0, 1))

@[simp] theorem affineGlobalPair_apply (q : R × R →ₗ[R] M)
    (a b : Γ(Spec R, ⊤)) :
    affineGlobalPair M q (a, b) = a • (1 ⊗ₜ[R] q (1, 0)) + b • (1 ⊗ₜ[R] q (0, 1)) := rfl

theorem affineGlobalPair_surjective (q : R × R →ₗ[R] M) (hq : Function.Surjective q) :
    Function.Surjective (affineGlobalPair M q) := by
  intro z
  obtain ⟨a, b, hz⟩ := extended_pair_generates q hq z
  exact ⟨(a, b), hz.symm⟩

variable [Module.Finite R M] [Module.Projective R M]
  (hrank : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = 1)

/-- A principal neighborhood derived from rank-one projectivity at the given prime. -/
def affineFrameElement (p : PrimeSpectrum R) : R :=
  (exists_principal_section_frame M p (hrank p)).choose

theorem affineFrameElement_notMem (p : PrimeSpectrum R) :
    affineFrameElement M hrank p ∉ p.asIdeal :=
  (exists_principal_section_frame M p (hrank p)).choose_spec.1

/-- The chosen frame is a frame of associated-sheaf sections. -/
def affineSectionFrame (p : PrimeSpectrum R) :
    PrincipalSections M (affineFrameElement M hrank p) ≃ₗ[
      PrincipalRing (affineFrameElement M hrank p)] PrincipalRing (affineFrameElement M hrank p) :=
  (exists_principal_section_frame M p (hrank p)).choose_spec.2.some

theorem affineFrameCover :
    IsOpenCover (fun p : PrimeSpectrum R => principalOpen (affineFrameElement M hrank p)) := by
  apply top_le_iff.mp
  intro p hp
  exact Opens.mem_iSup.mpr ⟨p, affineFrameElement_notMem M hrank p⟩

/-- These are the exact `ModuleOn` frames consumed by the already proved gluing theorem. -/
def affineModuleOnFrame (p : PrimeSpectrum R) :
    ModuleOn (Q := AffineGlobalModule M) (principalOpen (affineFrameElement M hrank p)) ≃ₗ[
      RingOn (principalOpen (affineFrameElement M hrank p))]
      RingOn (principalOpen (affineFrameElement M hrank p)) :=
  principalModuleOnFrame M _ (affineSectionFrame M hrank p)

/-- Affine rank-one quotients yield scheme morphisms without supplied local frames. -/
def fromFiniteProjectivePair (q : R × R →ₗ[R] M) (hq : Function.Surjective q) :
    Spec R ⟶ ProjectiveLine.scheme R :=
  fromFrames (affineGlobalPair M q) (affineGlobalPair_surjective M q hq)
    (affineModuleOnFrame M hrank) (algebraMap R Γ(Spec R, ⊤)) (affineFrameCover M hrank)

/-- Restriction recovers the two quotient sections in their constructed local frame. -/
theorem restrict_fromFiniteProjectivePair
    (q : R × R →ₗ[R] M) (hq : Function.Surjective q) (p : PrimeSpectrum R) :
    let f := affineFrameElement M hrank p
    let frame := affineSectionFrame M hrank p
    (principalOpen f).ι ≫ fromFiniteProjectivePair M hrank q hq =
      ProjectiveLine.fromPair
        (ProjectiveLine.coefficientsOn (algebraMap R Γ(Spec R, ⊤)) (principalOpen f))
        ((principalOpen f).topIso.inv (frame (principalToSections M f (q (1, 0)))))
        ((principalOpen f).topIso.inv (frame (principalToSections M f (q (0, 1)))))
        ((principal_section_coordinates_coprime M f q hq frame).map
          (principalOpen f).topIso.inv.hom) := by
  dsimp only
  simpa only [fromFiniteProjectivePair, affineModuleOnFrame, affineGlobalPair_apply, zero_smul,
    one_smul, add_zero, zero_add, principalModuleOnFrame_one_tmul] using
    restrict_fromFrames (affineGlobalPair M q) (affineGlobalPair_surjective M q hq)
      (affineModuleOnFrame M hrank) (algebraMap R Γ(Spec R, ⊤)) (affineFrameCover M hrank) p

/-- The resulting projective morphism is over `Spec R`. -/
@[reassoc] theorem fromFiniteProjectivePair_toSpec
    (q : R × R →ₗ[R] M) (hq : Function.Surjective q) :
    fromFiniteProjectivePair M hrank q hq ≫ ProjectiveLine.toSpec R = 𝟙 (Spec R) := by
  rw [fromFiniteProjectivePair, fromFrames_toSpec]
  change (Spec R).toSpecΓ ≫ Spec.map (Scheme.ΓSpecIso R).inv = _
  exact toSpecΓ_SpecMap_ΓSpecIso_inv R

variable {M}

/-- A two-dimensional Grassmannian quotient supplies all module hypotheses. -/
def fromAffineGrassmannian (K : Module.Grassmannian R (R × R) 1) :
    Spec R ⟶ ProjectiveLine.scheme R :=
  fromFiniteProjectivePair (ModuleCat.of R ((R × R) ⧸ K.toSubmodule))
    K.rankAtStalk_eq K.toSubmodule.mkQ K.toSubmodule.mkQ_surjective

theorem fromAffineGrassmannian_toSpec (K : Module.Grassmannian R (R × R) 1) :
    fromAffineGrassmannian K ≫ ProjectiveLine.toSpec R = 𝟙 (Spec R) := by
  simp only [fromAffineGrassmannian, fromFiniteProjectivePair_toSpec]

end FlagVarieties.Foundations.QuotientPair
