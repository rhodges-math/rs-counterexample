import Schubert.RS.Sl2PrimitiveCompletion
import Schubert.RS.RankOneCompletionTransport
import Schubert.RS.Representation.RankOneTensorCompletion

namespace Schubert.RS.Representation
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

def twistedPrimitiveBoundary : V →ₗ[ℂ] (V ⊗[ℂ] fullPrimitiveModule t P) :=
  ((fullPrimitiveBoundary t P).lTensor V).comp (TensorProduct.rid ℂ V).symm.toLinearMap

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
end Schubert.RS.Representation
