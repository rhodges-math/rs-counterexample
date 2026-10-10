import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.AlgebraMap

namespace Schubert.RS.Representation
noncomputable section

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

/-- Apply a linear functional coefficient by coefficient. Multiplicativity
is neither required nor asserted. -/
def polynomialMapLinear (f : A →ₗ[K] K) (p : _root_.Polynomial A) : _root_.Polynomial K :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff (p.toFinsupp.coeff.mapRange f (map_zero f)))

theorem polynomialMapLinear_coeff (f : A →ₗ[K] K) (p : _root_.Polynomial A) (k : ℕ) :
    (polynomialMapLinear f p).coeff k = f (p.coeff k) := rfl

theorem polynomialMapLinear_add (f : A →ₗ[K] K) (p q : _root_.Polynomial A) :
    polynomialMapLinear f (p+q) = polynomialMapLinear f p + polynomialMapLinear f q := by
  ext k
  simp [polynomialMapLinear_coeff]

theorem polynomialMapLinear_monomial (f : A →ₗ[K] K) (k : ℕ) (a : A) :
    polynomialMapLinear f (Polynomial.monomial k a) = Polynomial.monomial k (f a) := by
  ext j
  simp only [polynomialMapLinear_coeff,Polynomial.coeff_monomial]
  split_ifs <;> simp

theorem polynomialMapLinear_eval (f : A →ₗ[K] K) (p : _root_.Polynomial A) (t : K) :
    (polynomialMapLinear f p).eval t = f (p.eval (algebraMap K A t)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [polynomialMapLinear_add,Polynomial.eval_add,Polynomial.eval_add,
      f.map_add,hp,hq]
  | monomial k a =>
    rw [polynomialMapLinear_monomial,Polynomial.eval_monomial,Polynomial.eval_monomial]
    have h : a * (algebraMap K A t)^k = (t^k) • a := by
      rw [Algebra.smul_def,map_pow,mul_comm]
    rw [h,f.map_smul,smul_eq_mul,mul_comm]

/-- Over an infinite field, a vector polynomial taking all scalar values
in a subspace has every coefficient in that subspace. -/
theorem polynomial_coeff_mem_of_eval_mem [Infinite K] (S : Submodule K A)
    (p : _root_.Polynomial A) (h : ∀ t : K, p.eval (algebraMap K A t) ∈ S) (k : ℕ) :
    p.coeff k ∈ S := by
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff S _).mp
  intro f hf
  have hz : polynomialMapLinear f p = 0 := by
    apply Polynomial.funext
    intro t
    rw [polynomialMapLinear_eval,Polynomial.eval_zero]
    exact (S.mem_dualAnnihilator f).mp hf _ (h t)
  have hc := congrArg (fun q : _root_.Polynomial K => q.coeff k) hz
  simpa only [polynomialMapLinear_coeff,Polynomial.coeff_zero] using hc

end
end Schubert.RS.Representation
