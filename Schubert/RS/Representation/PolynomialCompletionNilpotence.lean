import Schubert.RS.PolynomialRootCompletion

namespace Schubert.RS.Representation
noncomputable section
universe u
open TensorProduct Module.End
open scoped BigOperators
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

theorem end_nilpotent_of_polynomial_embedding {n : ℕ} {X : Type*}
    [AddCommGroup X] [Module ℂ X] [Module.Finite ℂ X]
    (a b : Fin n) (hab : a≠b) (D : Module.End ℂ X)
    (f : X →ₗ[ℂ] MatrixPolynomial n) (hf : Function.Injective f)
    (hd : ∀ x, f (D x)=matrixUnitDerivation a b (f x)) : IsNilpotent D := by
  have hp : ∀ k x, f ((D^k) x)=derivationIter (matrixUnitDerivation a b) k (f x) := by
    intro k x
    induction k with
    | zero => rfl
    | succ k ih => rw [end_pow_succ_apply,hd,ih,derivationIter_succ]
  apply end_nilpotent_of_locally_nilpotent
  intro x
  obtain ⟨k,hk⟩ := matrixUnit_locally_nilpotent a b hab (f x)
  exact ⟨k,hf ((hp k x).trans (hk.trans (f.map_zero).symm))⟩

theorem polynomialIrreducible_root_nilpotent {n : ℕ} (a b : Fin n) (hab : a≠b) (d : ℕ)
    (z : (polynomialSl2Triple a b hab).toLieSubalgebra ℂ)
    (c e : Fin n) (hce : c≠e) (hz : z.val=(matrixUnitDerivation c e).toLinearMap) :
    IsNilpotent (LieModule.toEnd ℂ _ (polynomialIrreducible a b hab d) z) := by
  let f : polynomialIrreducible a b hab d →ₗ[ℂ] MatrixPolynomial n :=
    { toFun := fun x => x.val.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply end_nilpotent_of_polynomial_embedding c e hce _ f
  · intro x y hxy
    exact Subtype.ext (Subtype.ext hxy)
  · intro x
    change z.val x.val.val=matrixUnitDerivation c e x.val.val
    rw [hz]
    rfl

theorem tensor_toEnd_nilpotent {L R X : Type*} [LieRing L] [LieAlgebra ℂ L]
    [AddCommGroup R] [Module ℂ R] [LieRingModule L R] [LieModule ℂ L R]
    [AddCommGroup X] [Module ℂ X] [LieRingModule L X] [LieModule ℂ L X]
    (a : L) (hR : IsNilpotent (LieModule.toEnd ℂ L R a))
    (hX : IsNilpotent (LieModule.toEnd ℂ L X a)) :
    IsNilpotent (LieModule.toEnd ℂ L (R ⊗[ℂ] X) a) := by
  have heq : LieModule.toEnd ℂ L (R ⊗[ℂ] X) a =
      (LieModule.toEnd ℂ L R a).rTensor X + (LieModule.toEnd ℂ L X a).lTensor R :=
    TensorProduct.ext' (fun r x => TensorProduct.LieModule.lie_tmul_right a r x)
  rw [heq]
  have hc : Commute ((LieModule.toEnd ℂ L R a).rTensor X) ((LieModule.toEnd ℂ L X a).lTensor R) := by ext; simp
  exact hc.isNilpotent_add (hR.map (rTensorAlgHom ℂ R X)) (hX.map (lTensorAlgHom ℂ X R))

theorem pi_toEnd_nilpotent {L : Type*} {I : Type u} [LieRing L] [LieAlgebra ℂ L] [Fintype I]
    (X : I → Type u) [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)]
    [∀ j, LieRingModule L (X j)] [∀ j, LieModule ℂ L (X j)]
    (a : L) (hj : ∀ j, IsNilpotent (LieModule.toEnd ℂ L (X j) a)) :
    IsNilpotent (LieModule.toEnd ℂ L (∀ j, X j) a) := by
  classical
  choose k hk using hj
  have hp : ∀ t x j, ((LieModule.toEnd ℂ L (∀ j, X j) a ^ t) x) j =
      (LieModule.toEnd ℂ L (X j) a ^ t) (x j) := by
    intro t x j
    induction t with
    | zero => rfl
    | succ t ih =>
        rw [end_pow_succ_apply,end_pow_succ_apply]
        change LieModule.toEnd ℂ L (X j) a (((LieModule.toEnd ℂ L (∀ j, X j) a ^ t) x) j)=_
        rw [ih]
  refine ⟨∑ j,k j,LinearMap.ext (fun x => funext (fun j => ?_))⟩
  change ((LieModule.toEnd ℂ L (∀ j, X j) a ^ (∑ j,k j)) x) j=0
  rw [hp]
  exact end_pow_apply_zero_of_le _ (x j)
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
    (LinearMap.congr_fun (hk j) (x j))

theorem PolynomialRootStringBasis.completedRoot_nilpotent {n : ℕ} {a b : Fin n}
    {S : Submodule ℂ (MatrixPolynomial n)} (B : PolynomialRootStringBasis a b S) (hab : a≠b)
    (z : (polynomialSl2Triple a b hab).toLieSubalgebra ℂ)
    (c e : Fin n) (hce : c≠e) (hz : z.val=(matrixUnitDerivation c e).toLinearMap) :
    IsNilpotent (LieModule.toEnd ℂ _ (B.completedModule hab) z) := by
  apply pi_toEnd_nilpotent
  intro j
  exact tensor_toEnd_nilpotent z
    (polynomialIrreducible_root_nilpotent a b hab (B.length j) z c e hce hz)
    (polynomialIrreducible_root_nilpotent a b hab (B.residual j) z c e hce hz)

end
end Schubert.RS.Representation
