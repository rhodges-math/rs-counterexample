import Schubert.RS.Representation.RankOneActionExtension

namespace Schubert.RS.Representation
noncomputable section
universe u v
open LieModule Module TensorProduct

variable {L : Type v} [LieRing L] [LieAlgebra ℂ L]
  {M X R N : Type u} [AddCommGroup M] [Module ℂ M]
  [AddCommGroup X] [Module ℂ X] [LieRingModule L X] [LieModule ℂ L X]
  [Module.Finite ℂ X] {e h : L} {E H : Module.End ℂ M} {ι : M →ₗ[ℂ] X}
  (C : IsRankOneCompletion e h E H ι)
  [AddCommGroup R] [Module ℂ R] [LieRingModule L R] [LieModule ℂ L R]
  [Module.Finite ℂ R]
  [AddCommGroup N] [Module ℂ N] [LieRingModule L N] [LieModule ℂ L N]
  [Module.Finite ℂ N]
  (ρ : (R ⊗[ℂ] M) →ₗ[ℂ] M)
  (he : ∀ z, ρ (tensorBorelOperator e E z) = E (ρ z))
  (hh : ∀ z, ρ (tensorBorelOperator h H z) = H (ρ z))

/-- Every equivariant map out of a completion which respects the source
action also respects its uniquely extended radical action. -/
theorem IsRankOneCompletion.extendAction_natural
    (A : (R ⊗[ℂ] N) →ₗ⁅ℂ,L⁆ N) (F : X →ₗ⁅ℂ,L⁆ N)
    (hF : ∀ r m, F (ι (ρ (r ⊗ₜ[ℂ] m))) = A (r ⊗ₜ[ℂ] F (ι m))) :
    F.comp (C.extendAction ρ he hh) =
      A.comp (TensorProduct.LieModule.map (LieModuleHom.id : R →ₗ⁅ℂ,L⁆ R) F) := by
  apply (C.tensor R).hom_ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r m =>
      change F (C.extendAction ρ he hh (r ⊗ₜ[ℂ] ι m)) = A (r ⊗ₜ[ℂ] F (ι m))
      rw [C.extendAction_boundary]
      exact hF r m
  | add z w hz hw => simp only [map_add,hz,hw]

theorem IsRankOneCompletion.extendAction_natural_apply
    (A : (R ⊗[ℂ] N) →ₗ⁅ℂ,L⁆ N) (F : X →ₗ⁅ℂ,L⁆ N)
    (hF : ∀ r m, F (ι (ρ (r ⊗ₜ[ℂ] m))) = A (r ⊗ₜ[ℂ] F (ι m)))
    (r : R) (x : X) :
    F (C.extendAction ρ he hh (r ⊗ₜ[ℂ] x)) = A (r ⊗ₜ[ℂ] F x) :=
  congrArg (fun f : (R ⊗[ℂ] X) →ₗ⁅ℂ,L⁆ N => f (r ⊗ₜ[ℂ] x))
    (C.extendAction_natural ρ he hh A F hF)

end
end Schubert.RS.Representation
