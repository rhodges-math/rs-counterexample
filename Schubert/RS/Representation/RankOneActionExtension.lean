import Schubert.RS.Representation.RankOneTensorCoherence

namespace Schubert.RS.Representation
noncomputable section
universe u v
open LieModule Module TensorProduct

variable {L : Type v} [LieRing L] [LieAlgebra ℂ L]
  {M X R : Type u} [AddCommGroup M] [Module ℂ M]
  [AddCommGroup X] [Module ℂ X] [LieRingModule L X] [LieModule ℂ L X]
  [Module.Finite ℂ X] {e h : L} {E H : Module.End ℂ M} {ι : M →ₗ[ℂ] X}
  (C : IsRankOneCompletion e h E H ι)
  [AddCommGroup R] [Module ℂ R] [LieRingModule L R] [LieModule ℂ L R]
  [Module.Finite ℂ R]
  (ρ : (R ⊗[ℂ] M) →ₗ[ℂ] M)
  (he : ∀ z, ρ (tensorBorelOperator e E z) = E (ρ z))
  (hh : ∀ z, ρ (tensorBorelOperator h H z) = H (ρ z))

/-- Extend an actual Borel-equivariant bilinear action using the proved
tensor universal property. Lie-action identities are proved separately. -/
def IsRankOneCompletion.extendAction : (R ⊗[ℂ] X) →ₗ⁅ℂ,L⁆ X :=
  (C.tensor R).lift (ι.comp ρ)
    (fun z => by change ι (ρ (tensorBorelOperator e E z)) = ⁅e,ι (ρ z)⁆; rw [he,C.map_e])
    (fun z => by change ι (ρ (tensorBorelOperator h H z)) = ⁅h,ι (ρ z)⁆; rw [hh,C.map_h])

theorem IsRankOneCompletion.extendAction_boundary (r : R) (m : M) :
    C.extendAction ρ he hh (r ⊗ₜ[ℂ] ι m) = ι (ρ (r ⊗ₜ[ℂ] m)) :=
  (C.tensor R).lift_boundary _ _ _ (r ⊗ₜ[ℂ] m)

theorem IsRankOneCompletion.extendAction_equivariant (a : L) (r : R) (x : X) :
    ⁅a,C.extendAction ρ he hh (r ⊗ₜ[ℂ] x)⁆ =
      C.extendAction ρ he hh (⁅a,r⁆ ⊗ₜ[ℂ] x) +
        C.extendAction ρ he hh (r ⊗ₜ[ℂ] ⁅a,x⁆) := by
  rw [← LieModuleHom.map_lie,TensorProduct.LieModule.lie_tmul_right,map_add]

theorem IsRankOneCompletion.extendAction_unique
    (A : (R ⊗[ℂ] X) →ₗ⁅ℂ,L⁆ X)
    (hA : ∀ r m, A (r ⊗ₜ[ℂ] ι m) = ι (ρ (r ⊗ₜ[ℂ] m))) : A = C.extendAction ρ he hh := by
  apply (C.tensor R).hom_ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r m => exact (hA r m).trans (C.extendAction_boundary ρ he hh r m).symm
  | add z w hz hw => simp only [map_add,hz,hw]

end
end Schubert.RS.Representation
