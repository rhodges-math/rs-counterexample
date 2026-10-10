import RSCounterexample.Demazure.Sl2PrimitiveCompletion
import RSCounterexample.Demazure.RankOneCompletionTransport
import RSCounterexample.Demazure.Representation.RankOneTensorCompletion

/-!
# Twisted completions

For a finite-dimensional module `V` over the subalgebra of an `sl₂`-triple,
`V ⊗ (primitive string of weight d)` is a rank-one completion of `V`, with raising acting on `V` and
the Cartan element shifted by `d` (`twistedPrimitiveCompletion`).
-/

namespace Demazure.FlagModule
noncomputable section
open LieModule Module TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]
  {h e f : L} (t : IsSl2Triple h e f)
  {M : Type} [AddCommGroup M] [Module ℂ M]
  [LieRingModule (t.toLieSubalgebra ℂ) M] [LieModule ℂ (t.toLieSubalgebra ℂ) M]
  [Module.Finite ℂ M] {m : M} {d : ℕ}
  (P : (sl2SubalgebraTriple t).HasPrimitiveVectorWith m (d:ℂ))
  (V : Type) [AddCommGroup V] [Module ℂ V]
  [LieRingModule (t.toLieSubalgebra ℂ) V] [LieModule ℂ (t.toLieSubalgebra ℂ) V]
  [Module.Finite ℂ V]

/-- The map `x ↦ x ⊗ v₀` from `V` to its tensor product with the full primitive string module, where
`v₀` is the top vector. -/
def twistedPrimitiveBoundary : V →ₗ[ℂ] (V ⊗[ℂ] fullPrimitiveModule t P) :=
  ((fullPrimitiveBoundary t P).lTensor V).comp (TensorProduct.rid ℂ V).symm.toLinearMap

omit [LieRingModule (t.toLieSubalgebra ℂ) V] [LieModule ℂ (t.toLieSubalgebra ℂ) V]
  [Module.Finite ℂ V] in
theorem twistedPrimitiveBoundary_apply (x : V) :
    twistedPrimitiveBoundary t P V x=x ⊗ₜ[ℂ] fullPrimitiveBasis t P 0 := by
  simp [twistedPrimitiveBoundary,TensorProduct.rid_symm_apply,fullPrimitiveBoundary_apply]

/-- Completion of any finite root representation twisted by a dominant
weight line. In particular this supplies every admissible terminal string. -/
theorem twistedPrimitiveCompletion :
    IsRankOneCompletion (sl2RaisingElement t) (sl2CartanElement t)
      (LieModule.toEnd ℂ (t.toLieSubalgebra ℂ) V (sl2RaisingElement t))
      (LieModule.toEnd ℂ (t.toLieSubalgebra ℂ) V (sl2CartanElement t)+
        (d:ℂ) • LinearMap.id) (twistedPrimitiveBoundary t P V) := by
  apply ((fullPrimitiveCompletion t P).tensor V).reparametrize (TensorProduct.rid ℂ V).symm
  · intro x
    simp [TensorProduct.rid_symm_apply,tensorBorelOperator_tmul]
  · intro x
    simp only [LinearMap.add_apply,LinearMap.smul_apply,LinearMap.id_apply,map_add,map_smul,
      TensorProduct.rid_symm_apply,tensorBorelOperator_tmul]
    rw [TensorProduct.tmul_smul]
    rfl

end
end Demazure.FlagModule
