import RSCounterexample.FlagVarieties.Foundations.Schemes.QuotientPairOpenFrames

/-!
# Projective morphisms from local frames of an extended quotient module

The ordered pair is the image of the standard basis under the given quotient
map. Coprimality and overlap units are derived by the preceding algebraic
bridge. This is not an assertion that an arbitrary quotient sheaf has such
a global module presentation or that local frames have been constructed.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientPair

open AlgebraicGeometry CategoryTheory TensorProduct TopologicalSpace

universe u v

attribute [local instance] openAlgebra

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {ι : Type v}
  {U : ι → X.Opens} {Q : Type u} [AddCommGroup Q] [Module Γ(X, ⊤) Q]
  (q : Γ(X, ⊤) × Γ(X, ⊤) →ₗ[Γ(X, ⊤)] Q) (hq : Function.Surjective q)
  (frames : ∀ i, ModuleOn (Q := Q) (U i) ≃ₗ[RingOn (U i)] RingOn (U i))
  (φ : R →+* Γ(X, ⊤)) (hU : IsOpenCover U)

/-- A surjective ordered quotient and local tensor-module frames define a scheme map. -/
def fromFrames : X ⟶ ProjectiveLine.scheme R :=
  (openPairData q hq frames).glue φ hU

/-- The local coordinates are exactly the two standard quotient images in the chosen frame. -/
@[reassoc] theorem restrict_fromFrames (i : ι) :
    (U i).ι ≫ fromFrames q hq frames φ hU =
      ProjectiveLine.fromPair (ProjectiveLine.coefficientsOn φ (U i))
        (frames i (1 ⊗ₜ[Γ(X, ⊤)] q (1, 0)))
        (frames i (1 ⊗ₜ[Γ(X, ⊤)] q (0, 1)))
        (frame_coordinates_coprime q hq (frames i)) :=
  (openPairData q hq frames).restrict_glue φ hU i

@[reassoc] theorem fromFrames_toSpec :
    fromFrames q hq frames φ hU ≫ ProjectiveLine.toSpec R =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) :=
  (openPairData q hq frames).glue_toSpec φ hU

set_option backward.isDefEq.respectTransparency false in
/-- No choice of local quotient frame affects the glued scheme morphism. -/
theorem fromFrames_eq
    (frames' : ∀ i, ModuleOn (Q := Q) (U i) ≃ₗ[RingOn (U i)] RingOn (U i)) :
    fromFrames q hq frames φ hU = fromFrames q hq frames' φ hU := by
  apply (X.openCoverOfIsOpenCover U hU).hom_ext
  intro i
  change ι at i
  change (U i).ι ≫ fromFrames q hq frames φ hU =
    (U i).ι ≫ fromFrames q hq frames' φ hU
  rw [restrict_fromFrames, restrict_fromFrames]
  obtain ⟨unit, hδ, hε⟩ := quotient_frame_change_pair (frames' i) (frames i)
    (1 ⊗ₜ[Γ(X, ⊤)] q (1, 0)) (1 ⊗ₜ[Γ(X, ⊤)] q (0, 1))
  simp only [hδ, hε]
  exact ProjectiveLine.fromPair_unit_mul _ _ _ (frame_coordinates_coprime q hq (frames' i)) unit

variable (K : Submodule Γ(X, ⊤) (Γ(X, ⊤) × Γ(X, ⊤)))

/-- In particular, a quotient by a submodule supplies the surjection automatically. -/
def fromQuotientFrames
    (frames : ∀ i, ModuleOn (Q := (Γ(X, ⊤) × Γ(X, ⊤)) ⧸ K) (U i) ≃ₗ[RingOn (U i)]
      RingOn (U i)) : X ⟶ ProjectiveLine.scheme R :=
  fromFrames K.mkQ K.mkQ_surjective frames φ hU

@[reassoc] theorem fromQuotientFrames_toSpec
    (frames : ∀ i, ModuleOn (Q := (Γ(X, ⊤) × Γ(X, ⊤)) ⧸ K) (U i) ≃ₗ[RingOn (U i)]
      RingOn (U i)) :
    fromQuotientFrames φ hU K frames ≫ ProjectiveLine.toSpec R =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) :=
  fromFrames_toSpec K.mkQ K.mkQ_surjective frames φ hU

end FlagVarieties.Foundations.QuotientPair
