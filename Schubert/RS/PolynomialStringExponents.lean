import Schubert.RS.PolynomialResidualExponent

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation Schubert
attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ} {a b : Fin n} {S : Submodule ℂ (MatrixPolynomial n)}
  (B : PolynomialRootStringBasis a b S) (hab : a≠b)

def PolynomialRootStringBasis.partialExponent (j : Σ i,Fin (B.length i+1)) : Fin n →₀ ℕ :=
  B.residualExponent j.1+Finsupp.single a (B.length j.1-j.2.val)+Finsupp.single b j.2.val

include hab in
theorem PolynomialRootStringBasis.partialExponent_weight (j : Σ i,Fin (B.length i+1)) :
    exponentWeight (B.partialExponent j)=B.normalizedWeight j := by
  have hw := B.residualExponent_weight hab j.1
  have hk : j.2.val≤B.length j.1 := by omega
  funext c
  have hc := congrFun hw c
  change (B.residualExponent j.1 c:ℤ)=_ at hc
  change (B.partialExponent j c:ℤ)=_
  by_cases hca : c=a
  · subst c
    simp [PolynomialRootStringBasis.residualWeight,hab] at hc
    simp [PolynomialRootStringBasis.partialExponent,PolynomialRootStringBasis.normalizedWeight,
      positiveRoot,hab,Nat.cast_sub hk,hc]
  by_cases hcb : c=b
  · subst c
    simp [PolynomialRootStringBasis.residualWeight] at hc
    simp [PolynomialRootStringBasis.partialExponent,PolynomialRootStringBasis.normalizedWeight,
      positiveRoot,hab.symm,Nat.cast_sub hk,hc]
    omega
  · simp [PolynomialRootStringBasis.residualWeight,hcb] at hc
    simpa [PolynomialRootStringBasis.partialExponent,PolynomialRootStringBasis.normalizedWeight,
      positiveRoot,hca,hcb] using hc

variable {i : AdjacentPosition n} (B' : PolynomialRootStringBasis i.left i.right S)

def PolynomialRootStringBasis.completedExponent (j : B'.completionIndex) : Fin n →₀ ℕ :=
  Finsupp.single i.left (B'.length j.1-j.2.1.val)+Finsupp.single i.right j.2.1.val+
    replaceAdjacentExponents (B'.residualExponent j.1) i
      (B'.residualExponent j.1 i.left-j.2.2.val)
      (B'.residualExponent j.1 i.right+j.2.2.val)

theorem PolynomialRootStringBasis.completedExponent_weight (j : B'.completionIndex) :
    exponentWeight (B'.completedExponent j)=B'.completionWeight j := by
  have hl := B'.residualExponent_left i.left_ne_right j.1
  have hr := B'.residualExponent_right i.left_ne_right j.1
  have hk : j.2.1.val≤B'.length j.1 := by omega
  have hg := B'.residualExponent_gap i.left_ne_right j.1
  have hq : j.2.2.val≤B'.residualExponent j.1 i.left := by have ht:=j.2.2.isLt; omega
  funext c
  change (B'.completedExponent j c:ℤ)=_
  by_cases hcl : c=i.left
  · subst c
    rw [PolynomialRootStringBasis.completedExponent,Finsupp.add_apply,Finsupp.add_apply,
      replaceAdjacentExponents_left]
    simp [PolynomialRootStringBasis.completionWeight,positiveRoot,i.left_ne_right,
      Nat.cast_sub hk,Nat.cast_sub hq,hl]
    omega
  by_cases hcr : c=i.right
  · subst c
    rw [PolynomialRootStringBasis.completedExponent,Finsupp.add_apply,Finsupp.add_apply,
      replaceAdjacentExponents_right]
    simp [PolynomialRootStringBasis.completionWeight,positiveRoot,i.left_ne_right.symm,hr]
    omega
  · rw [PolynomialRootStringBasis.completedExponent,Finsupp.add_apply,Finsupp.add_apply,
      replaceAdjacentExponents_of_ne _ _ _ _ _ hcl hcr]
    have hc := congrFun (B'.residualExponent_weight i.left_ne_right j.1) c
    change (B'.residualExponent j.1 c:ℤ)=_ at hc
    simpa [PolynomialRootStringBasis.residualWeight,PolynomialRootStringBasis.completionWeight,
      positiveRoot,hcl,hcr] using hc

end
end Schubert.RS.Representation
