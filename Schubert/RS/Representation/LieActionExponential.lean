import Schubert.RS.Representation.TensorExponentialCovariance

namespace Schubert.RS.Representation
noncomputable section
open TensorProduct
set_option maxHeartbeats 2000000

variable {L R X : Type*} [LieRing L] [LieAlgebra ℂ L]
  [AddCommGroup R] [Module ℂ R] [Module ℚ R] [LieRingModule L R] [LieModule ℂ L R]
  [AddCommGroup X] [Module ℂ X] [Module ℚ X] [LieRingModule L X] [LieModule ℂ L X]

theorem lie_tensor_operator (a : L) :
    (LieModule.toEnd ℂ L R a).rTensor X + (LieModule.toEnd ℂ L X a).lTensor R =
      LieModule.toEnd ℂ L (R ⊗[ℂ] X) a := by
  apply TensorProduct.ext'
  intro r x
  exact (TensorProduct.LieModule.lie_tmul_right a r x).symm

theorem LieModuleHom.exp_tensor_covariance
    (ρ : R ⊗[ℂ] X →ₗ⁅ℂ,L⁆ X) (a : L)
    (hR : IsNilpotent (LieModule.toEnd ℂ L R a))
    (hX : IsNilpotent (LieModule.toEnd ℂ L X a)) (r : R) (x : X) :
    IsNilpotent.exp (LieModule.toEnd ℂ L X a) (ρ (r ⊗ₜ[ℂ] x)) =
      ρ (IsNilpotent.exp (LieModule.toEnd ℂ L R a) r ⊗ₜ[ℂ]
        IsNilpotent.exp (LieModule.toEnd ℂ L X a) x) := by
  apply tensor_action_exp _ _ hR hX ρ.toLinearMap _ r x
  rw [lie_tensor_operator]
  apply LinearMap.ext
  intro z
  exact (ρ.map_lie a z).symm

variable (X) in
/-- The algebraic exponential of an actual nilpotent operator is invertible. -/
def nilpotentExpEquiv (D : Module.End ℂ X) (hD : IsNilpotent D) : X ≃ₗ[ℂ] X where
  toLinearMap := IsNilpotent.exp D
  invFun := fun x => IsNilpotent.exp (-D) x
  left_inv x := by
    change (IsNilpotent.exp (-D) * IsNilpotent.exp D) x = x
    rw [hD.exp_neg_mul_exp_self]
    rfl
  right_inv x := by
    change (IsNilpotent.exp D * IsNilpotent.exp (-D)) x = x
    rw [hD.exp_mul_exp_neg_self]
    rfl

def nilpotentWeylEquiv (E F : Module.End ℂ X) (hE : IsNilpotent E) (hF : IsNilpotent F) : X ≃ₗ[ℂ] X :=
  (nilpotentExpEquiv X E hE).trans
    ((nilpotentExpEquiv X (-F) hF.neg).trans (nilpotentExpEquiv X E hE))

theorem nilpotentWeylEquiv_apply (E F : Module.End ℂ X) (hE : IsNilpotent E)
    (hF : IsNilpotent F) (x : X) :
    nilpotentWeylEquiv E F hE hF x =
      IsNilpotent.exp E (IsNilpotent.exp (-F) (IsNilpotent.exp E x)) := rfl

theorem LieModuleHom.weyl_tensor_covariance
    (ρ : R ⊗[ℂ] X →ₗ⁅ℂ,L⁆ X) (e f : L)
    (heR : IsNilpotent (LieModule.toEnd ℂ L R e))
    (hfR : IsNilpotent (LieModule.toEnd ℂ L R f))
    (heX : IsNilpotent (LieModule.toEnd ℂ L X e))
    (hfX : IsNilpotent (LieModule.toEnd ℂ L X f)) (r : R) (x : X) :
    nilpotentWeylEquiv _ _ heX hfX (ρ (r ⊗ₜ[ℂ] x)) =
      ρ (nilpotentWeylEquiv _ _ heR hfR r ⊗ₜ[ℂ] nilpotentWeylEquiv _ _ heX hfX x) := by
  have hnegR : IsNilpotent (LieModule.toEnd ℂ L R (-f)) := by simpa only [map_neg] using hfR.neg
  have hnegX : IsNilpotent (LieModule.toEnd ℂ L X (-f)) := by simpa only [map_neg] using hfX.neg
  simp only [nilpotentWeylEquiv_apply]
  have hn := LieModuleHom.exp_tensor_covariance ρ (-f) hnegR hnegX
  simp only [map_neg] at hn
  rw [LieModuleHom.exp_tensor_covariance ρ e heR heX,hn,
    LieModuleHom.exp_tensor_covariance ρ e heR heX]

end
end Schubert.RS.Representation
