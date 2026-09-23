import Schubert.RS.CompositionPresentation

namespace Schubert.RS.Representation
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
end Schubert.RS.Representation
