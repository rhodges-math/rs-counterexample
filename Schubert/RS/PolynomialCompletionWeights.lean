import Schubert.RS.PolynomialCompletionTorus

namespace Schubert.RS.Representation
noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 2000000

variable {n : ℕ} {a b : Fin n} {S : Submodule ℂ (MatrixPolynomial n)}
  (B : PolynomialRootStringBasis a b S) (hab : a≠b)

include hab in
theorem PolynomialRootStringBasis.residual_cast_int (i : B.index) :
    (B.residual i:ℤ)=B.weight i a-B.weight i b+(B.length i:ℤ) :=
  Int.toNat_of_nonneg (polynomial_string_admissible a b hab (B.seed i) (B.weight i)
    (B.seed_weight i) (B.length i) (B.top_ne_zero i) (B.next_zero i))

include hab in
theorem PolynomialRootStringBasis.completionWeight_nonnegative (j : B.completionIndex) :
    ∀ c, 0≤B.completionWeight j c := by
  have ht := polynomial_weight_nonnegative _ (B.top_ne_zero j.1)
    (B.weight j.1+B.length j.1 • positiveRoot a b)
    (matrixUnit_derivationIter_weight a b (B.seed j.1) (B.weight j.1)
      (B.seed_weight j.1) (B.length j.1))
  have hb : 0≤B.weight j.1 b-(B.length j.1:ℤ) := by
    simpa [positiveRoot,hab,hab.symm] using ht b
  have hq := B.residual_cast_int hab j.1
  have hk : j.2.1.val≤B.length j.1 := by omega
  have hl : j.2.2.val≤B.residual j.1 := by omega
  intro c
  by_cases hc : c=a
  · subst c
    simp only [PolynomialRootStringBasis.completionWeight,Pi.add_apply,Pi.smul_apply,
      positiveRoot,Pi.sub_apply,Pi.single_apply,ite_true,if_neg hab,sub_zero,
      smul_eq_mul,mul_one]
    omega
  by_cases hc' : c=b
  · subst c
    simp only [PolynomialRootStringBasis.completionWeight,Pi.add_apply,Pi.smul_apply,
      positiveRoot,Pi.sub_apply,Pi.single_apply,ite_true,if_neg hab.symm,zero_sub,
      smul_eq_mul,mul_neg,mul_one]
    omega
  · simpa [PolynomialRootStringBasis.completionWeight,positiveRoot,hc,hc'] using ht c

def PolynomialRootStringBasis.completionCharacter : RS.Polynomial n :=
  labelledCharacter (fun j : B.completionIndex => nonnegativeWeightExponent (B.completionWeight j))

theorem PolynomialRootStringBasis.hasCompletionCharacter :
    HasTorusCharacter (B.completionTorus hab) B.completionCharacter := by
  apply hasTorusCharacter_of_eigenbasis _ (B.completionBasis hab)
    (fun j => nonnegativeWeightExponent (B.completionWeight j))
  intro t j
  rw [nonnegativeWeightExponent_weight _ (B.completionWeight_nonnegative hab j)]
  exact basisWeightTorus_basis (B.completionBasis hab) B.completionWeight t j

end
end Schubert.RS.Representation
