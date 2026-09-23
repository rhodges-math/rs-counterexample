import Schubert.RS.JosephPolo.LoweringRootValues

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
set_option maxHeartbeats 1600000

theorem function_pow_of_commuting_correction {R : Type*} [Ring R]
    (D : R → R) (E Z : R) (hD : D 1=0) (hrec : ∀ a, D (E*a)=E*D a+Z*a)
    (hEZ : Commute E Z) (k : ℕ) : D (E^(k+1))=(k+1) • (E^k*Z) := by
  induction k with
  | zero => simpa [hD] using hrec 1
  | succ k ih =>
    calc
      D (E^(k+1+1)) = E*((k+1) • (E^k*Z))+Z*E^(k+1) := by rw [pow_succ', hrec, ih]
      _ = (k+1) • (E^(k+1)*Z)+E^(k+1)*Z := by
        rw [mul_smul_comm, ← mul_assoc, ← pow_succ', ← (hEZ.pow_left (k+1)).eq]
      _ = (k+1+1) • (E^(k+1)*Z) := by simp only [add_nsmul, one_nsmul]

theorem loweringEnveloping_nonsimple_pow {n : ℕ} (i : AdjacentPosition n) (w : ℂ)
    (r : PositiveRoot n) (hr : r≠adjacentPositiveRoot i)
    (hc : Commute (rootOperator r) (UniversalEnvelopingAlgebra.ι ℂ (loweringUpper i (rootVector r))))
    (k : ℕ) :
    loweringEnveloping i w (rootOperator r^(k+1)) =
      (k+1) • (rootOperator r^k * UniversalEnvelopingAlgebra.ι ℂ (loweringUpper i (rootVector r))) := by
  apply function_pow_of_commuting_correction _ _ _ (loweringEnveloping_one i w) _ hc k
  intro a
  change loweringEnveloping i w (UniversalEnvelopingAlgebra.ι ℂ (rootVector r)*a) = _
  rw [loweringEnveloping_generator_mul, upperSimpleCoefficient_root_ne i r hr, zero_smul, sub_zero]
  rfl

theorem loweringEnveloping_simple_mul {n : ℕ} (i : AdjacentPosition n) (w : ℂ) (a : Enveloping n) :
    loweringEnveloping i w (rootOperator (adjacentPositiveRoot i)*a) =
      rootOperator (adjacentPositiveRoot i)*loweringEnveloping i w a -
        (cartanEnveloping (adjacentCartanDiagonal i) a+w • a) := by
  change loweringEnveloping i w (UniversalEnvelopingAlgebra.ι ℂ (rootVector (adjacentPositiveRoot i))*a) = _
  rw [loweringEnveloping_generator_mul, loweringUpper_simple, map_zero, zero_mul,
    upperSimpleCoefficient_simple, one_smul, zero_sub]
  exact (sub_eq_add_neg _ _).symm

theorem loweringEnveloping_simple_pow {n : ℕ} (i : AdjacentPosition n) (w : ℂ) (k : ℕ) :
    loweringEnveloping i w (rootOperator (adjacentPositiveRoot i)^(k+1)) =
      -(((k+1 : ℕ) : ℂ)*(w+(k : ℂ))) • rootOperator (adjacentPositiveRoot i)^k := by
  induction k with
  | zero =>
    have h := loweringEnveloping_simple_mul i w 1
    simpa [loweringEnveloping_one, cartanEnveloping_one] using h
  | succ k ih =>
    rw [pow_succ', loweringEnveloping_simple_mul, ih, cartanEnveloping_root_pow]
    have he : adjacentCartanDiagonal i (adjacentPositiveRoot i).val.1 -
        adjacentCartanDiagonal i (adjacentPositiveRoot i).val.2 = 2 := adjacentCartan_simple_weight i
    rw [he, mul_smul_comm, ← pow_succ']
    push_cast
    module

theorem loweringEnveloping_simple_relation {n : ℕ} (i : AdjacentPosition n) (m : ℕ) :
    loweringEnveloping i (-(m : ℂ)) (rootOperator (adjacentPositiveRoot i)^(m+1))=0 := by
  rw [loweringEnveloping_simple_pow]
  simp

end
end Schubert.RS.Representation
