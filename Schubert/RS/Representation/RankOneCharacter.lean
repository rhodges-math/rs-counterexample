import Schubert.RS.Representation.RankOne
import Schubert.RS.MonomialOperators
import Mathlib.Algebra.BigOperators.Intervals

namespace Schubert.RS.Representation

open FinPermutation Schubert
open scoped BigOperators
noncomputable section

/-- Positive-root weights of the rank-one JP quotient generated at the
adjacent swap of the dominant endpoint `a`. -/
def stringWeight {n : ℕ} (i : AdjacentPosition n) (a : Fin n →₀ ℕ)
    (k : Fin (a i.left - a i.right + 1)) : Fin n →₀ ℕ :=
  replaceAdjacentExponents a i (a i.right + k) (a i.left - k)

/-- Distinct quotient degrees have distinct torus weight labels. -/
theorem stringWeight_injective {n : ℕ} (i : AdjacentPosition n)
    (a : Fin n →₀ ℕ) : Function.Injective (stringWeight i a) := by
  intro k l h
  apply Fin.ext
  have he := congrArg (fun w : Fin n →₀ ℕ => w i.left) h
  simp only [stringWeight, replaceAdjacentExponents_left] at he
  omega

/-- The character computed from the homogeneous lines of the actual
rank-one quotient equals the operator-defined rank-one key. -/
theorem cyclicCharacter_eq_isobaric {n : ℕ} (i : AdjacentPosition n)
    (a : Fin n →₀ ℕ) (h : a i.right ≤ a i.left) :
    cyclicCharacter (a i.left - a i.right) (stringWeight i a) =
      isobaric i (MvPolynomial.monomial a 1) := by
  classical
  rw [cyclicCharacter_eq_sum, isobaric_monomial i a h]
  change (∑ k : Fin (a i.left - a i.right + 1),
    MvPolynomial.monomial
      (replaceAdjacentExponents a i (a i.right + (k : ℕ)) (a i.left - (k : ℕ))) (1 : ℤ)) = _
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => MvPolynomial.monomial
    (replaceAdjacentExponents a i (a i.right + k) (a i.left - k)) (1 : ℤ))]
  rw [← Finset.sum_range_reflect
    (fun k => MvPolynomial.monomial
      (replaceAdjacentExponents a i (a i.left - k) (a i.right + k)) (1 : ℤ))
    (a i.left - a i.right + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < a i.left - a i.right + 1 := Finset.mem_range.mp hk
  have hleft : a i.right + k = a i.left - (a i.left - a i.right + 1 - 1 - k) := by omega
  have hright : a i.left - k = a i.right + (a i.left - a i.right + 1 - 1 - k) := by omega
  rw [hleft, hright]

end
end Schubert.RS.Representation
