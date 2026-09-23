import Schubert.RS.PolynomialStringExponents

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation Schubert
open scoped BigOperators
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 2000000

variable {n : ℕ} {i : AdjacentPosition n} {S : Submodule ℂ (MatrixPolynomial n)}
  (B : PolynomialRootStringBasis i.left i.right S)

theorem PolynomialRootStringBasis.partialCharacter_eq :
    labelledCharacter B.partialExponent=
      ∑ j, partialStringCharacter i (B.residualExponent j) (B.length j) := by
  classical
  unfold labelledCharacter
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j hj
  rw [partialStringCharacter_sum]
  exact Fin.sum_univ_eq_sum_range (fun k => MvPolynomial.monomial
    (B.residualExponent j+Finsupp.single i.left (B.length j-k)+Finsupp.single i.right k) (1:ℤ)) _

theorem PolynomialRootStringBasis.completedCharacter_eq :
    labelledCharacter B.completedExponent=
      ∑ j, completedStringCharacter i (B.residualExponent j) (B.length j) := by
  classical
  unfold labelledCharacter
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Fintype.sum_prod_type,completedStringCharacter_sum i _
    (B.residualExponent_dominant i.left_ne_right j),B.residualExponent_gap i.left_ne_right j]
  simp only [PolynomialRootStringBasis.completedExponent]
  let f : ℕ → ℕ → RS.Polynomial n := fun k l => MvPolynomial.monomial
    (Finsupp.single i.left (B.length j-k)+Finsupp.single i.right k+
      replaceAdjacentExponents (B.residualExponent j) i
        (B.residualExponent j i.left-l) (B.residualExponent j i.right+l)) (1:ℤ)
  change (∑ k : Fin (B.length j+1), ∑ l : Fin (B.residual j+1), f k.val l.val)=_
  rw [Fin.sum_univ_eq_sum_range (fun k => ∑ l : Fin (B.residual j+1), f k l.val)]
  apply Finset.sum_congr rfl
  intro k hk
  exact Fin.sum_univ_eq_sum_range (f k) _

theorem PolynomialRootStringBasis.hasPartialCharacter :
    HasTorusCharacter B.sourceTorus
      (∑ j, partialStringCharacter i (B.residualExponent j) (B.length j)) := by
  letI : FiniteDimensional ℂ S := Module.Finite.of_basis B.normalizedBasis
  rw [← B.partialCharacter_eq]
  apply hasTorusCharacter_of_eigenbasis _ B.normalizedBasis B.partialExponent
  intro t j
  rw [B.partialExponent_weight i.left_ne_right j]
  exact basisWeightTorus_basis B.normalizedBasis B.normalizedWeight t j

theorem PolynomialRootStringBasis.hasCompletedStringCharacter :
    HasTorusCharacter (B.completionTorus i.left_ne_right)
      (∑ j, completedStringCharacter i (B.residualExponent j) (B.length j)) := by
  rw [← B.completedCharacter_eq]
  apply hasTorusCharacter_of_eigenbasis _ (B.completionBasis i.left_ne_right) B.completedExponent
  intro t j
  rw [B.completedExponent_weight j]
  exact basisWeightTorus_basis (B.completionBasis i.left_ne_right) B.completionWeight t j

/-- The character of the finite completion is the isobaric transform of
the source character. Comparison with a neighboring flag module is separate. -/
theorem PolynomialRootStringBasis.completion_character_recursion
    (p : RS.Polynomial n) (hp : HasTorusCharacter B.sourceTorus p) :
    HasTorusCharacter (B.completionTorus i.left_ne_right) (isobaric i p) := by
  rw [hp.unique B.hasPartialCharacter]
  have hh : isobaric i (∑ j, partialStringCharacter i (B.residualExponent j) (B.length j))=
      ∑ j, completedStringCharacter i (B.residualExponent j) (B.length j) := by
    change adjacentDividedDifference i (MvPolynomial.X i.left * _)=_
    rw [Finset.mul_sum,map_sum]
    exact Finset.sum_congr rfl (fun j _ => partialStringCharacter_isobaric i _ _)
  rw [hh]
  exact B.hasCompletedStringCharacter

end
end Schubert.RS.Representation
