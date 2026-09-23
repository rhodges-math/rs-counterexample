import Schubert.RS.Representation.RankOneTensorCompletion

namespace Schubert.RS.Representation
noncomputable section
universe u v
open LieModule Module TensorProduct

variable {L : Type v} [LieRing L] [LieAlgebra ℂ L]
  (R S X : Type u) [AddCommGroup R] [Module ℂ R] [LieRingModule L R] [LieModule ℂ L R]
  [AddCommGroup S] [Module ℂ S] [LieRingModule L S] [LieModule ℂ L S]
  [AddCommGroup X] [Module ℂ X] [LieRingModule L X] [LieModule ℂ L X]

def lieTensorComm : (R ⊗[ℂ] S) ≃ₗ⁅ℂ,L⁆ (S ⊗[ℂ] R) :=
  { TensorProduct.comm ℂ R S with
    map_lie' := by
      intro a z
      change (TensorProduct.comm ℂ R S) ⁅a,z⁆ = ⁅a,(TensorProduct.comm ℂ R S) z⁆
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul r s => simp [TensorProduct.LieModule.lie_tmul_right,add_comm]
      | add z w hz hw => simp only [lie_add,map_add,hz,hw] }

@[simp] theorem lieTensorComm_tmul (r : R) (s : S) :
    lieTensorComm (L := L) R S (r ⊗ₜ[ℂ] s) = s ⊗ₜ[ℂ] r := rfl

def lieTensorAssoc : ((R ⊗[ℂ] S) ⊗[ℂ] X) ≃ₗ⁅ℂ,L⁆ (R ⊗[ℂ] (S ⊗[ℂ] X)) :=
  { TensorProduct.assoc ℂ R S X with
    map_lie' := by
      intro a z
      change (TensorProduct.assoc ℂ R S X) ⁅a,z⁆ = ⁅a,(TensorProduct.assoc ℂ R S X) z⁆
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul rs x =>
          induction rs using TensorProduct.induction_on with
          | zero => simp
          | tmul r s => simp [TensorProduct.LieModule.lie_tmul_right,
              TensorProduct.add_tmul,TensorProduct.tmul_add,add_assoc]
          | add rs st hrs hst => simp only [TensorProduct.add_tmul,lie_add,map_add,hrs,hst]
      | add z w hz hw => simp only [lie_add,map_add,hz,hw] }

@[simp] theorem lieTensorAssoc_tmul (r : R) (s : S) (x : X) :
    lieTensorAssoc (L := L) R S X ((r ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] x) = r ⊗ₜ[ℂ] (s ⊗ₜ[ℂ] x) := rfl

@[simp] theorem lieTensorAssoc_symm_tmul (r : R) (s : S) (x : X) :
    (lieTensorAssoc (L := L) R S X).symm (r ⊗ₜ[ℂ] (s ⊗ₜ[ℂ] x)) = (r ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] x := rfl

def lieTensorSwapFirst : (R ⊗[ℂ] (S ⊗[ℂ] X)) →ₗ⁅ℂ,L⁆ (S ⊗[ℂ] (R ⊗[ℂ] X)) :=
  (lieTensorAssoc (L := L) S R X).toLieModuleHom.comp
    ((TensorProduct.LieModule.map (lieTensorComm (L := L) R S).toLieModuleHom
      (LieModuleHom.id : X →ₗ⁅ℂ,L⁆ X)).comp
      (lieTensorAssoc (L := L) R S X).symm.toLieModuleHom)

@[simp] theorem lieTensorSwapFirst_tmul (r : R) (s : S) (x : X) :
    lieTensorSwapFirst (L := L) R S X (r ⊗ₜ[ℂ] (s ⊗ₜ[ℂ] x)) =
      s ⊗ₜ[ℂ] (r ⊗ₜ[ℂ] x) := rfl

end
end Schubert.RS.Representation
