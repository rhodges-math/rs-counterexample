import Schubert.TypeA.Polynomials.DividedDifferences
import Schubert.RS.Compositions

/-!
# Operators for keys and Demazure atoms

The isobaric operator is defined using the existing integral divided difference.
All statements here are proved; Joseph–Polo and PBW are not used in this file.
-/

namespace Schubert.RS

open FinPermutation Schubert

abbrev Polynomial (n : ℕ) := MvPolynomial (Fin n) ℤ

noncomputable section

variable {n : ℕ}

/-- The operator defining key polynomials. -/
def isobaric (i : AdjacentPosition n) (p : Polynomial n) : Polynomial n :=
  adjacentDividedDifference i (MvPolynomial.X i.left * p)

/-- The operator defining Demazure atoms. -/
def atomOperator (i : AdjacentPosition n) (p : Polynomial n) : Polynomial n :=
  isobaric i p - p

theorem isobaric_formula (i : AdjacentPosition n) (p : Polynomial n) :
    (MvPolynomial.X i.left - MvPolynomial.X i.right) * isobaric i p =
      MvPolynomial.X i.left * p -
        MvPolynomial.X i.right * adjacentVariableSwap i p := by
  simp only [isobaric, adjacentRoot_mul_adjacentDividedDifference,
    map_mul, adjacentVariableSwap_X_left]

theorem isobaric_eq (i : AdjacentPosition n) (p : Polynomial n) :
    isobaric i p = p + MvPolynomial.X i.right * adjacentDividedDifference i p := by
  simp [isobaric, adjacentDividedDifference_mul]

theorem atomOperator_eq (i : AdjacentPosition n) (p : Polynomial n) :
    atomOperator i p = MvPolynomial.X i.right * adjacentDividedDifference i p := by
  rw [atomOperator, isobaric_eq]
  abel

@[simp] theorem isobaric_zero (i : AdjacentPosition n) : isobaric i 0 = 0 := by
  simp [isobaric]

@[simp] theorem isobaric_add (i : AdjacentPosition n) (p q : Polynomial n) :
    isobaric i (p + q) = isobaric i p + isobaric i q := by
  simp [isobaric, mul_add]

@[simp] theorem isobaric_sub (i : AdjacentPosition n) (p q : Polynomial n) :
    isobaric i (p - q) = isobaric i p - isobaric i q := by
  simp [isobaric, mul_sub]

@[simp] theorem isobaric_smul (i : AdjacentPosition n) (z : ℤ) (p : Polynomial n) :
    isobaric i (z • p) = z • isobaric i p := by
  unfold isobaric
  rw [mul_smul_comm, map_smul]

theorem swap_isobaric (i : AdjacentPosition n) (p : Polynomial n) :
    adjacentVariableSwap i (isobaric i p) = isobaric i p :=
  adjacentVariableSwap_adjacentDividedDifference i _

theorem isobaric_of_symmetric (i : AdjacentPosition n) (p : Polynomial n)
    (hp : adjacentVariableSwap i p = p) : isobaric i p = p := by
  apply mul_left_cancel₀ (adjacentRoot_ne_zero i)
  rw [isobaric_formula, hp]
  ring

@[simp] theorem isobaric_idempotent (i : AdjacentPosition n) (p : Polynomial n) :
    isobaric i (isobaric i p) = isobaric i p :=
  isobaric_of_symmetric i _ (swap_isobaric i p)

@[simp] theorem atomOperator_square (i : AdjacentPosition n) (p : Polynomial n) :
    atomOperator i (atomOperator i p) = -atomOperator i p := by
  simp only [atomOperator, isobaric_sub, isobaric_idempotent]
  abel

theorem isobaric_mul_of_symmetric (i : AdjacentPosition n) (p q : Polynomial n)
    (hp : adjacentVariableSwap i p = p) :
    isobaric i (p * q) = p * isobaric i q := by
  apply mul_left_cancel₀ (adjacentRoot_ne_zero i)
  rw [isobaric_formula, map_mul, hp]
  calc
    _ = p * (MvPolynomial.X i.left * q -
        MvPolynomial.X i.right * adjacentVariableSwap i q) := by ring
    _ = _ := by rw [← isobaric_formula]; ring

end
end Schubert.RS
