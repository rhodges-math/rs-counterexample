import Schubert.RS.Operators
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-!
# K-theoretic isobaric operators

Polynomials in the deformation parameter `β` with coefficients in `ℤ[x₁, …, xₙ]` form
`BetaPolynomial n = (Polynomial n)[β]`. On them act the K-theoretic isobaric divided
differences of Lascoux, in the convention of Monical–Pechenik–Searles
(arXiv:1806.03802, Remark 4.24):
`πᵢ^{(β)} f = πᵢ((1 + β x_{i+1}) f)` and `π̄ᵢ^{(β)} = πᵢ^{(β)} - 1`,
where `πᵢ f = ∂ᵢ(xᵢ f)` is the isobaric divided difference `isobaric`.
With this sign of `β`, `πᵢ^{(β)} = 1 + x_{i+1}(1 + β xᵢ) ∂ᵢ` (`betaIsobaric_eq`).
Setting `β = 0` recovers `isobaric` and `atomOperator`.
-/

namespace Schubert.RS

open FinPermutation Schubert

noncomputable section

variable {n : ℕ}

/-- Polynomials in `β` with coefficients in `ℤ[x₁, …, xₙ]`. -/
abbrev BetaPolynomial (n : ℕ) := _root_.Polynomial (Polynomial n)

/-- The deformation parameter `β`. -/
abbrev beta : BetaPolynomial n := _root_.Polynomial.X

/-- The variable `x_j` as a constant polynomial in `β`. -/
def xβ (j : Fin n) : BetaPolynomial n := _root_.Polynomial.C (MvPolynomial.X j)

/-- A `ℤ`-linear operator on `ℤ[x]`, applied to each coefficient in `β`. -/
def betaLinear (L : Polynomial n →ₗ[ℤ] Polynomial n) :
    BetaPolynomial n →ₗ[ℤ] BetaPolynomial n :=
  _root_.Polynomial.lsum fun k =>
    ((_root_.Polynomial.monomial k : Polynomial n →ₗ[Polynomial n] BetaPolynomial n).restrictScalars
      ℤ).comp L

@[simp] theorem coeff_betaLinear (L : Polynomial n →ₗ[ℤ] Polynomial n) (f : BetaPolynomial n)
    (k : ℕ) : (betaLinear L f).coeff k = L (f.coeff k) := by
  rw [betaLinear, _root_.Polynomial.lsum_apply, _root_.Polynomial.coeff_sum,
    _root_.Polynomial.sum_def]
  simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars,
    _root_.Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with hk
  · rfl
  · rw [_root_.Polynomial.notMem_support_iff.mp hk, map_zero]

@[simp] theorem betaLinear_C (L : Polynomial n →ₗ[ℤ] Polynomial n) (p : Polynomial n) :
    betaLinear L (_root_.Polynomial.C p) = _root_.Polynomial.C (L p) := by
  refine _root_.Polynomial.ext fun k => ?_
  rw [coeff_betaLinear, _root_.Polynomial.coeff_C, _root_.Polynomial.coeff_C]
  split_ifs <;> simp

/-- The isobaric divided difference `πᵢ f = ∂ᵢ(xᵢ f)` as a `ℤ`-linear map. -/
def isobaricLinear (i : AdjacentPosition n) : Polynomial n →ₗ[ℤ] Polynomial n :=
  (adjacentDividedDifference i).comp (LinearMap.mulLeft ℤ (MvPolynomial.X i.left))

@[simp] theorem isobaricLinear_apply (i : AdjacentPosition n) (p : Polynomial n) :
    isobaricLinear i p = isobaric i p := rfl

/-- The divided difference `∂ᵢ` as a `ℤ`-linear map. -/
def dividedDifferenceLinear (i : AdjacentPosition n) : Polynomial n →ₗ[ℤ] Polynomial n :=
  adjacentDividedDifference i

/-- The K-theoretic isobaric divided difference `πᵢ^{(β)} f = πᵢ((1 + β x_{i+1}) f)`. -/
def betaIsobaric (i : AdjacentPosition n) (f : BetaPolynomial n) : BetaPolynomial n :=
  betaLinear (isobaricLinear i) ((1 + beta * xβ i.right) * f)

/-- The K-theoretic atom operator `π̄ᵢ^{(β)} = πᵢ^{(β)} - 1`. -/
def betaAtomOperator (i : AdjacentPosition n) (f : BetaPolynomial n) : BetaPolynomial n :=
  betaIsobaric i f - f

/-- `πᵢ(g + x_{i+1} h) = g + x_{i+1} ∂ᵢ g + x_{i+1} xᵢ ∂ᵢ h`, from the twisted Leibniz rule
and `∂ᵢ x_{i+1} = -1`. -/
theorem isobaric_add_X_right_mul (i : AdjacentPosition n) (g h : Polynomial n) :
    isobaric i (g + MvPolynomial.X i.right * h) =
      g + MvPolynomial.X i.right * adjacentDividedDifference i g +
        MvPolynomial.X i.right * MvPolynomial.X i.left * adjacentDividedDifference i h := by
  rw [isobaric_eq, map_add, adjacentDividedDifference_mul, adjacentDividedDifference_X_right,
    adjacentVariableSwap_X_right]
  ring

/-- The closed form `πᵢ^{(β)} = 1 + x_{i+1}(1 + β xᵢ) ∂ᵢ`. -/
theorem betaIsobaric_eq (i : AdjacentPosition n) (f : BetaPolynomial n) :
    betaIsobaric i f =
      f + xβ i.right * (1 + beta * xβ i.left) * betaLinear (dividedDifferenceLinear i) f := by
  refine _root_.Polynomial.ext fun k => ?_
  rcases k with _ | k
  · simp [betaIsobaric, xβ, mul_add, add_mul, mul_assoc, isobaric_eq, dividedDifferenceLinear]
  · have hL : ((1 + beta * xβ i.right) * f).coeff (k + 1) =
        f.coeff (k + 1) + MvPolynomial.X i.right * f.coeff k := by
      simp [xβ, add_mul, mul_assoc, _root_.Polynomial.coeff_X_mul]
    rw [betaIsobaric, coeff_betaLinear, hL, isobaricLinear_apply, isobaric_add_X_right_mul]
    simp [xβ, mul_add, add_mul, mul_assoc, _root_.Polynomial.coeff_X_mul, dividedDifferenceLinear]
    ring

/-- Specialization at `β = 0`. -/
def betaZero : BetaPolynomial n →+* Polynomial n := _root_.Polynomial.constantCoeff

theorem betaZero_apply (f : BetaPolynomial n) : betaZero f = f.coeff 0 := rfl

@[simp] theorem betaZero_C (p : Polynomial n) : betaZero (_root_.Polynomial.C p) = p := by
  simp [betaZero_apply]

@[simp] theorem betaZero_beta : betaZero (beta : BetaPolynomial n) = 0 := by
  simp [betaZero_apply]

@[simp] theorem betaZero_xβ (j : Fin n) : betaZero (xβ j) = MvPolynomial.X j := by
  simp [xβ]

theorem betaZero_betaLinear (L : Polynomial n →ₗ[ℤ] Polynomial n) (f : BetaPolynomial n) :
    betaZero (betaLinear L f) = L (betaZero f) := by
  simp [betaZero_apply]

/-- At `β = 0`, `πᵢ^{(β)}` is the isobaric divided difference `πᵢ`. -/
theorem betaZero_betaIsobaric (i : AdjacentPosition n) (f : BetaPolynomial n) :
    betaZero (betaIsobaric i f) = isobaric i (betaZero f) := by
  rw [betaIsobaric, betaZero_betaLinear, isobaricLinear_apply]
  congr 1
  simp

/-- At `β = 0`, `π̄ᵢ^{(β)}` is the atom operator `π̄ᵢ = πᵢ - 1`. -/
theorem betaZero_betaAtomOperator (i : AdjacentPosition n) (f : BetaPolynomial n) :
    betaZero (betaAtomOperator i f) = atomOperator i (betaZero f) := by
  rw [betaAtomOperator, map_sub, betaZero_betaIsobaric, atomOperator]

end
end Schubert.RS
