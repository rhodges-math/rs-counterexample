import Schubert.RS.Representation.StringFiltration

namespace Schubert.RS.Representation
noncomputable section

theorem HasTorusCharacter.of_equiv {n : ℕ} {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : DiagonalTorus n →* Module.End ℂ X} {σ : DiagonalTorus n →* Module.End ℂ Y}
    {p : RS.Polynomial n} (hp : HasTorusCharacter ρ p)
    (e : X ≃ₗ[ℂ] Y) (he : ∀ t x, e (ρ t x)=σ t (e x)) : HasTorusCharacter σ p := by
  intro w
  rw [← torusWeightSpace_finrank_eq ρ σ e he w]
  exact hp w

end
end Schubert.RS.Representation
