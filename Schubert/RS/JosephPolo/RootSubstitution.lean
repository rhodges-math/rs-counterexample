import Schubert.RS.Representation.MinorStrings
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Eval.Coeff

namespace Schubert.RS.Representation
noncomputable section
open scoped Polynomial

/-- Polynomial dependence on the parameter of an elementary row action. -/
def rootSubstitution {n : ℕ} (a b : Fin n) :
    MatrixPolynomial n →ₐ[ℂ] _root_.Polynomial (MatrixPolynomial n) :=
  MvPolynomial.aeval fun rc => Polynomial.C (MvPolynomial.X rc) +
    if rc.1 = b then Polynomial.X * Polynomial.C (MvPolynomial.X (a,rc.2)) else 0

theorem rootSubstitution_X {n : ℕ} (a b r c : Fin n) :
    rootSubstitution a b (MvPolynomial.X (r,c)) = Polynomial.C (MvPolynomial.X (r,c)) +
      if r=b then Polynomial.X * Polynomial.C (MvPolynomial.X (a,c)) else 0 :=
  MvPolynomial.aeval_X _ _

theorem rootSubstitution_C {n : ℕ} (a b : Fin n) (c : ℂ) :
    rootSubstitution a b (MvPolynomial.C c) = Polynomial.C (MvPolynomial.C c) := by
  exact (rootSubstitution a b).commutes c

theorem rootSubstitution_eval_zero {n : ℕ} (a b : Fin n) (p : MatrixPolynomial n) :
    (rootSubstitution a b p).eval 0 = p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [rootSubstitution_C]
  | add p q hp hq => simp [map_add,hp,hq]
  | mul_X p rc hp =>
    obtain ⟨r,c⟩ := rc
    rw [map_mul,Polynomial.eval_mul,hp,rootSubstitution_X]
    by_cases h : r=b <;> simp [h]

theorem rootSubstitution_derivative_X {n : ℕ} (a b : Fin n) (hab : a≠b) (r c : Fin n) :
    Polynomial.derivative (rootSubstitution a b (MvPolynomial.X (r,c))) =
      rootSubstitution a b (matrixUnitDerivation a b (MvPolynomial.X (r,c))) := by
  by_cases h : r=b
  · simp [rootSubstitution_X,matrixUnitDerivation_X,h,hab]
  · simp [rootSubstitution_X,matrixUnitDerivation_X,h]

/-- Differentiating the parameter agrees exactly with the Lie root action. -/
theorem rootSubstitution_derivative {n : ℕ} (a b : Fin n) (hab : a≠b)
    (p : MatrixPolynomial n) : Polynomial.derivative (rootSubstitution a b p) =
      rootSubstitution a b (matrixUnitDerivation a b p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [rootSubstitution_C,Derivation.map_algebraMap]
  | add p q hp hq => simp [map_add,hp,hq]
  | mul_X p rc hp =>
    obtain ⟨r,c⟩ := rc
    rw [map_mul,Polynomial.derivative_mul,hp,rootSubstitution_derivative_X a b hab,
      Derivation.leibniz,map_add]
    simp only [smul_eq_mul,map_mul]
    ring

theorem rootSubstitution_iterate_derivative {n : ℕ} (a b : Fin n) (hab : a≠b)
    (p : MatrixPolynomial n) (k : ℕ) :
    Polynomial.derivative^[k] (rootSubstitution a b p) =
      rootSubstitution a b (derivationIter (matrixUnitDerivation a b) k p) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih,rootSubstitution_derivative a b hab,derivationIter_succ]

/-- Exact Taylor coefficients, stated without division by factorials. -/
theorem rootSubstitution_coeff {n : ℕ} (a b : Fin n) (hab : a≠b)
    (p : MatrixPolynomial n) (k : ℕ) :
    k.factorial • (rootSubstitution a b p).coeff k =
      derivationIter (matrixUnitDerivation a b) k p := by
  have h := Polynomial.coeff_iterate_derivative (k:=k) (rootSubstitution a b p) 0
  rw [rootSubstitution_iterate_derivative a b hab] at h
  have hz : (rootSubstitution a b (derivationIter (matrixUnitDerivation a b) k p)).coeff 0 =
      derivationIter (matrixUnitDerivation a b) k p := by
    rw [Polynomial.coeff_zero_eq_eval_zero,rootSubstitution_eval_zero]
  simpa only [hz,Nat.zero_add,Nat.descFactorial_self] using h.symm

end
end Schubert.RS.Representation
