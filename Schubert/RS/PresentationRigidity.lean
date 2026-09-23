import Schubert.RS.CompositionPresentation

namespace Schubert.RS.Representation
noncomputable section

variable {n : ℕ} {X : Type*} [AddCommGroup X] [Module (Enveloping n) X]

/-- The U-linear orbit map requires neither a character nor a basis. -/
def presentationOrbitMap (ξ : X) : Enveloping n →ₗ[Enveloping n] X where
  toFun a := a • ξ
  map_add' a b := add_smul a b ξ
  map_smul' a b := mul_smul a b ξ

def presentationLift (u : Composition n) (ξ : X)
    (hξ : ∀ r : PositiveRoot n, (rootOperator r ^ jpExponent u r) • ξ = 0) :
    PresentationQuotient u →ₗ[Enveloping n] X :=
  (jpLeftIdeal u).liftQ (presentationOrbitMap ξ) (by
    apply Submodule.span_le.mpr
    rintro a ⟨r,rfl⟩
    exact hξ r)

theorem presentationLift_generator (u : Composition n) (ξ : X)
    (hξ : ∀ r : PositiveRoot n, (rootOperator r ^ jpExponent u r) • ξ = 0) :
    presentationLift u ξ hξ (presentationGenerator u) = ξ := by
  change (1 : Enveloping n) • ξ = ξ
  exact one_smul _ _

theorem presentationLift_surjective (u : Composition n) (ξ : X)
    (hξ : ∀ r : PositiveRoot n, (rootOperator r ^ jpExponent u r) • ξ = 0)
    (hcyc : ∀ x : X, ∃ a : Enveloping n, a • ξ = x) :
    Function.Surjective (presentationLift u ξ hξ) := by
  intro x
  obtain ⟨a,ha⟩ := hcyc x
  exact ⟨Submodule.Quotient.mk a,ha⟩

/-- Once JP is supplied for the actual target, another cyclic module with
the same defining relations cannot have a nontrivial kernel in a map to that
target preserving its generator. This needs no PBW, dimensions, or DCF. -/
theorem compositionPresentation_rigidity (u : Composition n)
    (hJP : CompositionFlagJosephPolo u) (ξ : X)
    (hξ : ∀ r : PositiveRoot n, (rootOperator r ^ jpExponent u r) • ξ = 0)
    (hcyc : ∀ x : X, ∃ a : Enveloping n, a • ξ = x)
    (f : X →ₗ[Enveloping n] compositionFlag u)
    (hf : f ξ = compositionFlagGenerator u) : Function.Bijective f := by
  obtain ⟨e,hgen,heq⟩ := hJP
  have hn (q : PresentationQuotient u) : f (presentationLift u ξ hξ q) = e q := by
    obtain ⟨a,rfl⟩ := presentation_is_cyclic u q
    rw [map_smul,map_smul,presentationLift_generator,hf,map_smul,hgen]
  constructor
  · intro x y hxy
    obtain ⟨p,rfl⟩ := presentationLift_surjective u ξ hξ hcyc x
    obtain ⟨q,rfl⟩ := presentationLift_surjective u ξ hξ hcyc y
    rw [hn,hn] at hxy
    exact congrArg (presentationLift u ξ hξ) (e.injective hxy)
  · intro p
    obtain ⟨q,hq⟩ := e.surjective p
    exact ⟨presentationLift u ξ hξ q,(hn q).trans hq⟩

end
end Schubert.RS.Representation
