import Schubert.RS.Operators
import Schubert.TypeA.Polynomials.DividedDifferenceRelations

/-! The braid and distant-commutation relations for the key and atom operators. -/

namespace Schubert.RS

open FinPermutation Schubert

noncomputable section
variable {n : ℕ}

theorem isobaric_braid (i j : AdjacentPosition n) (h : i.right = j.left)
    (p : Polynomial n) :
    isobaric i (isobaric j (isobaric i p)) =
      isobaric j (isobaric i (isobaric j p)) := by
  have hir : i.left ≠ j.right := (i.left_lt_right.trans (h ▸ j.left_lt_right)).ne
  have hjr : j.right ≠ i.right := by rw [h]; exact j.left_ne_right.symm
  have hd : adjacentDividedDifference i (MvPolynomial.X j.left) = -1 := by
    simpa only [h] using adjacentDividedDifference_X_right i
  simp only [isobaric_eq, map_add, adjacentDividedDifference_mul,
    adjacentDividedDifference_X_right, adjacentVariableSwap_X_right,
    adjacentDividedDifference_X_other i j.right hir.symm hjr,
    adjacentVariableSwap_X_other i j.right hir.symm hjr,
    h, hd, adjacentDividedDifference_X_left, adjacentVariableSwap_X_left,
    zero_mul, one_mul, neg_one_mul,
    mul_zero, zero_add, add_zero, adjacentDividedDifference_sq]
  rw [adjacentDividedDifference_braid i j h p]
  ring

theorem isobaric_commute (i j : AdjacentPosition n)
    (h : SeparatedAdjacentPositions i j) (p : Polynomial n) :
    isobaric i (isobaric j p) = isobaric j (isobaric i p) := by
  obtain ⟨hll, hlr, hrl, hrr⟩ := separated_endpoint_ne i j h
  simp only [isobaric_eq, map_add, adjacentDividedDifference_mul,
    adjacentDividedDifference_X_other i j.right hlr.symm hrr.symm,
    adjacentVariableSwap_X_other i j.right hlr.symm hrr.symm,
    adjacentDividedDifference_X_other j i.right hrl hrr,
    adjacentVariableSwap_X_other j i.right hrl hrr,
    zero_mul, zero_add]
  rw [adjacentDividedDifference_commute_of_separated i j h p]
  ring

theorem atomOperator_braid (i j : AdjacentPosition n) (h : i.right = j.left)
    (p : Polynomial n) :
    atomOperator i (atomOperator j (atomOperator i p)) =
      atomOperator j (atomOperator i (atomOperator j p)) := by
  simp only [atomOperator, isobaric_sub, isobaric_idempotent]
  rw [isobaric_braid i j h p]
  abel

theorem atomOperator_commute (i j : AdjacentPosition n)
    (h : SeparatedAdjacentPositions i j) (p : Polynomial n) :
    atomOperator i (atomOperator j p) = atomOperator j (atomOperator i p) := by
  simp only [atomOperator, isobaric_sub]
  rw [isobaric_commute i j h p]
  abel

end
end Schubert.RS
