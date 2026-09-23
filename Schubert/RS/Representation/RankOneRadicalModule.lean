import Schubert.RS.Representation.RankOneActionJacobi

namespace Schubert.RS.Representation
noncomputable section
universe u v
open LieModule Module TensorProduct

variable {L : Type v} [LieRing L] [LieAlgebra ℂ L]
  {R M X : Type u} [LieRing R] [LieAlgebra ℂ R]
  [LieRingModule L R] [LieModule ℂ L R] [Module.Finite ℂ R]
  [AddCommGroup M] [Module ℂ M]
  [AddCommGroup X] [Module ℂ X] [LieRingModule L X] [LieModule ℂ L X]
  [Module.Finite ℂ X] {e h : L} {E H : Module.End ℂ M} {ι : M →ₗ[ℂ] X}
  (C : IsRankOneCompletion e h E H ι)
  (ρ : (R ⊗[ℂ] M) →ₗ[ℂ] M)
  (he : ∀ z, ρ (tensorBorelOperator e E z) = E (ρ z))
  (hh : ∀ z, ρ (tensorBorelOperator h H z) = H (ρ z))
  (hder : ∀ (a : L) (r s : R), ⁅a,⁅r,s⁆⁆ = ⁅⁅a,r⁆,s⁆ + ⁅r,⁅a,s⁆⁆)
  (hρ : ∀ r s m, ρ (⁅r,s⁆ ⊗ₜ[ℂ] m) =
    ρ (r ⊗ₜ[ℂ] ρ (s ⊗ₜ[ℂ] m)) - ρ (s ⊗ₜ[ℂ] ρ (r ⊗ₜ[ℂ] m)))

/-- The extended action is a genuine Lie-ring-module structure on the
exhibited completion. Its Jacobi axiom is derived by tensor uniqueness. -/
@[instance_reducible] def IsRankOneCompletion.radicalLieRingModule : LieRingModule R X where
  bracket r x := C.extendAction ρ he hh (r ⊗ₜ[ℂ] x)
  add_lie r s x := by simp only [TensorProduct.add_tmul,map_add]
  lie_add r x y := by simp only [TensorProduct.tmul_add,map_add]
  leibniz_lie r s x := by
    have hj := C.action_jacobi hder ρ (C.extendAction ρ he hh)
      (C.extendAction_boundary ρ he hh) hρ r s x
    exact (sub_eq_iff_eq_add.mp hj.symm)

/-- Scalar compatibility of the newly constructed radical action. -/
@[instance_reducible] def IsRankOneCompletion.radicalLieModule :
    @LieModule ℂ R X _ _ _ _ _ (C.radicalLieRingModule ρ he hh hder hρ) := by
  letI := C.radicalLieRingModule ρ he hh hder hρ
  exact
    { smul_lie := fun c r x => by
        change C.extendAction ρ he hh ((c • r) ⊗ₜ[ℂ] x) = c • C.extendAction ρ he hh (r ⊗ₜ[ℂ] x)
        rw [← TensorProduct.smul_tmul',map_smul]
      lie_smul := fun c r x => by
        change C.extendAction ρ he hh (r ⊗ₜ[ℂ] (c • x)) = c • C.extendAction ρ he hh (r ⊗ₜ[ℂ] x)
        rw [TensorProduct.tmul_smul,map_smul] }

/-- The original rank-one action acts by derivations of the constructed
radical action, as required for the corresponding semidirect product. -/
theorem IsRankOneCompletion.radical_isLieTower :
    letI := C.radicalLieRingModule ρ he hh hder hρ
    IsLieTower L R X := by
  letI := C.radicalLieRingModule ρ he hh hder hρ
  refine ⟨?_⟩
  intro a r x
  exact C.extendAction_equivariant ρ he hh a r x

theorem IsRankOneCompletion.radical_boundary (r : R) (m : M) :
    letI := C.radicalLieRingModule ρ he hh hder hρ
    ⁅r,ι m⁆ = ι (ρ (r ⊗ₜ[ℂ] m)) :=
  C.extendAction_boundary ρ he hh r m

end
end Schubert.RS.Representation
