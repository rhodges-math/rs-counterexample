import RSCounterexample.Demazure.CompositionPresentation

/-!
# Maps between cyclic modules agree up to a scalar

If `U(𝔫⁺)`-linear maps `f` from the presentation quotient of `u` and `e` to the flag module send the
generator to `c⁻¹` times the flag generator, then `c • e ∘ f` is the canonical presentation map
(`presentation_maps_scalar`).
-/

open Schubert

namespace Demazure.FlagModule
noncomputable section

theorem presentation_maps_scalar {n : ℕ} (u : Composition n)
    {X : Type*} [AddCommGroup X] [Module (Enveloping n) X]
    (f : PresentationQuotient u →ₗ[Enveloping n] X)
    (e : X →ₗ[Enveloping n] compositionFlag u) (c : ℂ)
    (hgen : compositionFlagGenerator u = c • e (f (presentationGenerator u)))
    (q : PresentationQuotient u) : compositionPresentationMap u q = c • e (f q) := by
  obtain ⟨a,rfl⟩ := presentation_is_cyclic u q
  rw [map_smul,compositionPresentationMap_generator,hgen,f.map_smul,e.map_smul,smul_comm]

end
end Demazure.FlagModule
