import Schubert.RS.Lascoux.Polynomials

/-!
# The smallest Lascoux polynomial and Lascoux atom

A check of the sign convention for `β` in two variables `x₁ = X 0`, `x₂ = X 1`:
`𝔏_{01} = x₁ + x₂ + β x₁ x₂` and `𝔏̄_{01} = x₂ + β x₁ x₂`, as in Monical–Pechenik–Searles
(arXiv:1806.03802), where `β = -1` gives the Grothendieck polynomial `x₁ + x₂ - x₁ x₂`.
-/

namespace Schubert.RS

open FinPermutation Schubert

noncomputable section

private theorem ascentSet_zero_one : (ascentSet (![0, 1] : Composition 2)).Nonempty :=
  ⟨0, by decide⟩

private theorem firstAscent_zero_one :
    firstAscent ![0, 1] ascentSet_zero_one = ⟨0, by decide⟩ := by
  apply AdjacentPosition.ext
  apply Fin.ext
  have h := (firstAscent ![0, 1] ascentSet_zero_one).hasRight
  show (firstAscent ![0, 1] ascentSet_zero_one).left.val = 0
  omega

private theorem swapComposition_zero_one :
    swapComposition (![0, 1] : Composition 2) ⟨0, by decide⟩ = ![1, 0] := by
  funext j
  fin_cases j <;> rfl

private theorem compositionMonomial_one_zero :
    compositionMonomial (![1, 0] : Composition 2) = MvPolynomial.X 0 := by
  have h : Finsupp.equivFunOnFinite.symm (![1, 0] : Fin 2 → ℕ) = Finsupp.single 0 1 := by
    ext j
    fin_cases j <;> simp
  rw [compositionMonomial, h]
  rfl

private theorem lascoux_one_zero :
    lascoux (![1, 0] : Composition 2) = _root_.Polynomial.C (MvPolynomial.X 0) := by
  rw [lascoux_of_antitone _ (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all),
    compositionMonomial_one_zero]

private theorem lascouxAtom_one_zero :
    lascouxAtom (![1, 0] : Composition 2) = _root_.Polynomial.C (MvPolynomial.X 0) := by
  rw [lascouxAtom_of_antitone _ (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all),
    compositionMonomial_one_zero]

private theorem betaIsobaric_C_X_zero :
    betaIsobaric ⟨0, by decide⟩ (_root_.Polynomial.C (MvPolynomial.X (0 : Fin 2))) =
      _root_.Polynomial.C (MvPolynomial.X 0) + xβ 1 * (1 + beta * xβ 0) := by
  have h1 : dividedDifferenceLinear (⟨0, by decide⟩ : AdjacentPosition 2)
      (MvPolynomial.X 0) = 1 :=
    adjacentDividedDifference_X_left _
  rw [betaIsobaric_eq, betaLinear_C, h1, map_one, mul_one]
  rfl

/-- `𝔏_{01} = x₁ + x₂ + β x₁ x₂`. -/
theorem lascoux_zero_one :
    lascoux (![0, 1] : Composition 2) = xβ 0 + xβ 1 + beta * xβ 0 * xβ 1 := by
  rw [lascoux_ascent _ ascentSet_zero_one, firstAscent_zero_one, swapComposition_zero_one,
    lascoux_one_zero, betaIsobaric_C_X_zero]
  simp only [xβ]
  ring

/-- `𝔏̄_{01} = x₂ + β x₁ x₂`. -/
theorem lascouxAtom_zero_one :
    lascouxAtom (![0, 1] : Composition 2) = xβ 1 + beta * xβ 0 * xβ 1 := by
  rw [lascouxAtom_ascent _ ascentSet_zero_one, firstAscent_zero_one, swapComposition_zero_one,
    lascouxAtom_one_zero, betaAtomOperator, betaIsobaric_C_X_zero]
  ring

end
end Schubert.RS
