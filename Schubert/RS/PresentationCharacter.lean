import Schubert.RS.Representation.FullWeightSpaces
import Schubert.RS.Keys

/-! Presentation isomorphisms and Demazure characters.

HasJosephPoloPresentation specifies an enveloping-algebra isomorphism
compatible with the torus action and cyclic vector. HasDemazureCharacter
specifies the finite-dimensional full torus weight spaces and their dimensions.
The transport lemmas identify the character of the presentation quotient.
-/

namespace Schubert.RS
noncomputable section
open Representation

variable {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
  [Module (Enveloping n) E] [IsScalarTower ℂ (Enveloping n) E]

/-- A natural U(n+)-linear presentation isomorphism, compatible with the
full torus action and the specified extremal cyclic vector. -/
def HasJosephPoloPresentation (u : Composition n)
    (ρ : DiagonalTorus n →* Module.End ℂ E) (ξ : E) : Prop :=
  ∃ e : PresentationQuotient u ≃ₗ[Enveloping n] E,
    e (presentationGenerator u) = ξ ∧
      ∀ t x, e (jpTorusRepresentation u t x) = ρ t (e x)

/-- The Demazure character property on full torus weight spaces, including
finite dimensionality of each weight space. -/
def HasDemazureCharacter (u : Composition n)
    (ρ : DiagonalTorus n →* Module.End ℂ E) : Prop :=
  ∀ w : Weight n, FiniteDimensional ℂ (torusWeightSpace ρ w) ∧
    (Module.finrank ℂ (torusWeightSpace ρ w) : ℤ) = (toLaurent (key u)).coeff w

/-- Transport the character across the Joseph-Polo presentation isomorphism. -/
theorem jpWeight_coefficient (u : Composition n)
    (ρ : DiagonalTorus n →* Module.End ℂ E) (ξ : E)
    (hJP : HasJosephPoloPresentation u ρ ξ) (hDCF : HasDemazureCharacter u ρ) (w : Weight n) :
    (Module.finrank ℂ (torusWeightSpace (jpTorusRepresentation u) w) : ℤ) =
      (toLaurent (key u)).coeff w := by
  obtain ⟨e, hξ, he⟩ := hJP
  have hd := torusWeightSpace_finrank_eq (jpTorusRepresentation u) ρ
    (e.restrictScalars ℂ) he w
  rw [hd]
  exact (hDCF w).2

theorem jpWeight_finite (u : Composition n)
    (ρ : DiagonalTorus n →* Module.End ℂ E) (ξ : E)
    (hJP : HasJosephPoloPresentation u ρ ξ) (hDCF : HasDemazureCharacter u ρ) (w : Weight n) :
    FiniteDimensional ℂ (torusWeightSpace (jpTorusRepresentation u) w) := by
  obtain ⟨e, hξ, he⟩ := hJP
  letI := (hDCF w).1
  exact FiniteDimensional.of_injective
    (torusWeightSpaceEquiv (jpTorusRepresentation u) ρ (e.restrictScalars ℂ) he w).toLinearMap
    (torusWeightSpaceEquiv (jpTorusRepresentation u) ρ (e.restrictScalars ℂ) he w).injective

end
end Schubert.RS
