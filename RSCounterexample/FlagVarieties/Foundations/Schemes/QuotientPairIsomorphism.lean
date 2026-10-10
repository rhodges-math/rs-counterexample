import RSCounterexample.FlagVarieties.Foundations.Schemes.QuotientPairCoverIndependence

/-! # Projective morphisms respect isomorphisms of ordered quotient modules -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientPair

open AlgebraicGeometry CategoryTheory TensorProduct TopologicalSpace

universe u v w

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  {ι : Type v} {κ : Type w} {U : ι → X.Opens} {V : κ → X.Opens}
  {Q Q' : Type u} [AddCommGroup Q] [Module Γ(X, ⊤) Q]
  [AddCommGroup Q'] [Module Γ(X, ⊤) Q']

attribute [local instance] openAlgebra

/-- Transport a frame through a quotient-module isomorphism. -/
def transportQuotientFrame (e : Q ≃ₗ[Γ(X, ⊤)] Q') (A : X.Opens)
    (frame : ModuleOn (Q := Q') A ≃ₗ[RingOn A] RingOn A) :
    ModuleOn (Q := Q) A ≃ₗ[RingOn A] RingOn A :=
  e.baseChange Γ(X, ⊤) (RingOn A) Q Q' ≪≫ₗ frame

@[simp] theorem transportQuotientFrame_one_tmul (e : Q ≃ₗ[Γ(X, ⊤)] Q') (A : X.Opens)
    (frame : ModuleOn (Q := Q') A ≃ₗ[RingOn A] RingOn A) (x : Q) :
    transportQuotientFrame e A frame (1 ⊗ₜ[Γ(X, ⊤)] x) =
      frame (1 ⊗ₜ[Γ(X, ⊤)] e x) := by
  simp [transportQuotientFrame]

/-- Isomorphic ordered quotients give equal full scheme morphisms, even from different covers. -/
theorem fromFrames_quotient_equiv
    (q : Γ(X, ⊤) × Γ(X, ⊤) →ₗ[Γ(X, ⊤)] Q) (hq : Function.Surjective q)
    (q' : Γ(X, ⊤) × Γ(X, ⊤) →ₗ[Γ(X, ⊤)] Q') (hq' : Function.Surjective q')
    (e : Q ≃ₗ[Γ(X, ⊤)] Q') (he : ∀ x, e (q x) = q' x)
    (framesU : ∀ i, ModuleOn (Q := Q) (U i) ≃ₗ[RingOn (U i)] RingOn (U i))
    (framesV : ∀ j, ModuleOn (Q := Q') (V j) ≃ₗ[RingOn (V j)] RingOn (V j))
    (φ : R →+* Γ(X, ⊤)) (hU : IsOpenCover U) (hV : IsOpenCover V) :
    fromFrames q hq framesU φ hU = fromFrames q' hq' framesV φ hV := by
  rw [fromFrames_cover_independent q hq framesU
    (fun j => transportQuotientFrame e (V j) (framesV j)) φ hU hV]
  apply (X.openCoverOfIsOpenCover V hV).hom_ext
  intro j
  change (V j).ι ≫ _ = (V j).ι ≫ _
  rw [restrict_fromFrames, restrict_fromFrames]
  simp only [transportQuotientFrame_one_tmul, he]

end FlagVarieties.Foundations.QuotientPair
