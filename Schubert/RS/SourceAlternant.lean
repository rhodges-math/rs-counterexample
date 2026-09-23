import Schubert.RS.WeylDenominator
import Mathlib.LinearAlgebra.Vandermonde

/-! The finite Laurent Vandermonde identity at the start of source extraction. -/

namespace Schubert.RS

noncomputable section
variable {n : ℕ}

def coordinatePower (i : Fin n) (z : ℤ) : Laurent n :=
  AddMonoidAlgebra.single (Pi.single i z) 1

@[simp] theorem coordinatePower_zero (i : Fin n) : coordinatePower i 0 = 1 := by
  simp [coordinatePower, AddMonoidAlgebra.one_def]

theorem coordinatePower_add (i : Fin n) (a b : ℤ) :
    coordinatePower i (a + b) = coordinatePower i a * coordinatePower i b := by
  simp [coordinatePower, AddMonoidAlgebra.single_mul_single, Pi.single_add]

theorem coordinatePower_pow (i : Fin n) (a : ℤ) (k : ℕ) :
    coordinatePower i a ^ k = coordinatePower i ((k : ℤ) * a) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, ← coordinatePower_add]
    congr 1
    push_cast
    ring

theorem coordinate_inverse_difference (i j : Fin n) :
    coordinatePower j (-1) * (coordinatePower j 1 - coordinatePower i 1) =
      (1 : Laurent n) - AddMonoidAlgebra.single (positiveRoot i j) 1 := by
  rw [mul_sub, ← coordinatePower_add]
  simp only [neg_add_cancel, coordinatePower_zero]
  congr 1
  simp only [coordinatePower, AddMonoidAlgebra.single_mul_single, mul_one]
  apply congrArg (fun a : Weight n => AddMonoidAlgebra.single a (1 : ℤ))
  simp [positiveRoot, Pi.single_neg, sub_eq_add_neg, add_comm]

theorem upper_inverse_product :
    (∏ i : Fin n, ∏ j ∈ Finset.univ.filter (i < ·), coordinatePower j (-1)) =
      ∏ j : Fin n, coordinatePower j (-(j.val : ℤ)) := by
  simp only [Finset.prod_filter]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j _
  rw [← Finset.prod_filter]
  have hf : Finset.univ.filter (fun i : Fin n => i < j) = Finset.Iio j := by ext i; simp
  rw [hf, Finset.prod_const, Fin.card_Iio, coordinatePower_pow]
  congr 1
  ring

/-- The exact Laurent alternant, with the sign and exponent convention used
in the source-extraction determinant in the paper. -/
theorem weylFactor_eq_determinant :
    weylFactor n = Matrix.det
      (fun i j : Fin n => coordinatePower i ((j.val : ℤ) - i.val)) := by
  have hm : (fun i j : Fin n => coordinatePower i ((j.val : ℤ) - i.val)) =
      Matrix.of (fun i j : Fin n => coordinatePower i (-(i.val : ℤ)) *
        Matrix.vandermonde (fun k => coordinatePower k 1) i j) := by
    funext i j
    simp only [Matrix.of_apply, Matrix.vandermonde_apply, coordinatePower_pow,
      mul_one, ← coordinatePower_add]
    congr 1
    ring
  rw [hm, Matrix.det_mul_column, Matrix.det_vandermonde, weylFactor]
  have hf (i : Fin n) : Finset.univ.filter (i < ·) = Finset.Ioi i := by ext j; simp
  simp_rw [← coordinate_inverse_difference]
  simp only [Finset.prod_mul_distrib]
  rw [upper_inverse_product]
  simp only [hf]

end
end Schubert.RS
