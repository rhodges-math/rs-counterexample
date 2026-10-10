import RSCounterexample.Demazure.Operators

/-!
# The isobaric operator on monomials

For `a i.right ≤ a i.left`, the isobaric operator of the adjacent position `i` sends the monomial
`x^a` to the sum of the monomials of its rank-one string, obtained by moving exponent from `i.left`
to `i.right` (`isobaric_monomial`).
-/

open Schubert

namespace Demazure

open FinPermutation Schubert

noncomputable section
variable {n : ℕ}

/-- The rank-one character sum, obtained from the polynomial operator itself. -/
theorem isobaric_monomial (i : AdjacentPosition n) (a : Fin n →₀ ℕ)
    (h : a i.right ≤ a i.left) :
    isobaric i (MvPolynomial.monomial a 1) =
      ∑ k ∈ Finset.range (a i.left - a i.right + 1),
        MvPolynomial.monomial
          (replaceAdjacentExponents a i (a i.left - k) (a i.right + k)) 1 := by
  classical
  have hl : (Finsupp.single i.left 1 + a : Fin n →₀ ℕ) i.left = a i.left + 1 := by
      simp [Nat.add_comm]
  have hr : (Finsupp.single i.left 1 + a : Fin n →₀ ℕ) i.right = a i.right := by
    simp [i.left_ne_right.symm]
  have hlt : (Finsupp.single i.left 1 + a : Fin n →₀ ℕ) i.right <
      (Finsupp.single i.left 1 + a : Fin n →₀ ℕ) i.left := by rw [hl, hr]; omega
  unfold isobaric
  rw [MvPolynomial.X, MvPolynomial.monomial_mul_monomial]
  simp only [one_mul, adjacentDividedDifference_monomial_one]
  rw [monomialDividedDifference, dite_eq_left hlt, hl, hr]
  have hlen : a i.left + 1 - a i.right = a i.left - a i.right + 1 := by omega
  rw [hlen]
  apply Finset.sum_congr rfl
  intro k hk
  apply congrArg (fun d : Fin n →₀ ℕ => MvPolynomial.monomial d (1 : ℤ))
  ext j
  by_cases hjl : j = i.left
  · subst j
    simp
  · by_cases hjr : j = i.right
    · subst j
      simp
    · simp [replaceAdjacentExponents_of_ne _ _ _ _ _ hjl hjr,
        Finsupp.single_eq_of_ne hjl]

end
end Demazure
