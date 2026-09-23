import Schubert.RS.JosephPolo.LoweringRootValues

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1400000

theorem cartanMatrix_lie {n : ℕ} (h : Fin n → ℂ) (A B : Square n) :
    cartanMatrix h ⁅A,B⁆ = ⁅cartanMatrix h A,B⁆ + ⁅A,cartanMatrix h B⁆ := by
  change cartanMatrix h (A*B-B*A) =
    (cartanMatrix h A*B-B*cartanMatrix h A)+(A*cartanMatrix h B-cartanMatrix h B*A)
  rw [map_sub, cartanMatrix_mul, cartanMatrix_mul]
  abel

theorem cartanMatrix_single {n : ℕ} (h : Fin n → ℂ) (a b : Fin n) :
    cartanMatrix h (Matrix.single a b 1) = (h a-h b) • Matrix.single a b 1 := by
  ext j k
  change (h j-h k)*Matrix.single a b (1 : ℂ) j k = (h a-h b)*Matrix.single a b (1 : ℂ) j k
  simp only [Matrix.single_apply]
  split_ifs with hjk
  · rcases hjk with ⟨rfl,rfl⟩
    rfl
  · simp

theorem cartanMatrix_adjacent_lowering {n : ℕ} (i : AdjacentPosition n) :
    cartanMatrix (adjacentCartanDiagonal i) (Matrix.single i.right i.left 1) =
      (-2 : ℂ) • Matrix.single i.right i.left 1 := by
  rw [cartanMatrix_single]
  have he : adjacentCartanDiagonal i i.right-adjacentCartanDiagonal i i.left = -2 := by
    have h := adjacentCartan_simple_weight i
    linear_combination -h
  rw [he]

theorem cartanMatrix_adjacent_cartan {n : ℕ} (i : AdjacentPosition n) :
    cartanMatrix (adjacentCartanDiagonal i) (adjacentCartanMatrix i)=0 := by
  rw [adjacentCartanMatrix, map_sub, cartanMatrix_single, cartanMatrix_single]
  simp

theorem upperSimpleCoefficient_cartan {n : ℕ} (i : AdjacentPosition n) (A : upperNilpotent n) :
    upperSimpleCoefficient i (cartanUpper (adjacentCartanDiagonal i) A) =
      (2 : ℂ)*upperSimpleCoefficient i A := by
  rw [upperSimpleCoefficient_apply, upperSimpleCoefficient_apply]
  change (adjacentCartanDiagonal i i.left-adjacentCartanDiagonal i i.right)*A.val i.left i.right = _
  rw [adjacentCartan_simple_weight]

theorem loweringUpper_cartan {n : ℕ} (i : AdjacentPosition n) (A : upperNilpotent n) :
    loweringUpper i (cartanUpper (adjacentCartanDiagonal i) A) =
      cartanUpper (adjacentCartanDiagonal i) (loweringUpper i A)+(2 : ℂ) • loweringUpper i A := by
  apply Subtype.ext
  change ⁅(Matrix.single i.right i.left 1 : Square n),cartanMatrix (adjacentCartanDiagonal i) A.val⁆ +
    upperSimpleCoefficient i (cartanUpper (adjacentCartanDiagonal i) A) • adjacentCartanMatrix i =
    cartanMatrix (adjacentCartanDiagonal i)
      (⁅(Matrix.single i.right i.left 1 : Square n),A.val⁆ + upperSimpleCoefficient i A • adjacentCartanMatrix i) +
      (2 : ℂ) • (⁅(Matrix.single i.right i.left 1 : Square n),A.val⁆ + upperSimpleCoefficient i A • adjacentCartanMatrix i)
  rw [upperSimpleCoefficient_cartan, map_add, map_smul, cartanMatrix_lie,
    cartanMatrix_adjacent_lowering, cartanMatrix_adjacent_cartan, smul_zero, add_zero, smul_lie]
  simp only [smul_add, smul_smul]
  module

theorem loweringEnvelopingCocycle_cartan {n : ℕ} (i : AdjacentPosition n) (w : ℂ)
    (A : upperNilpotent n) :
    loweringEnvelopingCocycle i w (cartanUpper (adjacentCartanDiagonal i) A) =
      cartanEnveloping (adjacentCartanDiagonal i)*loweringEnvelopingCocycle i w A -
      loweringEnvelopingCocycle i w A*cartanEnveloping (adjacentCartanDiagonal i) +
      (2 : ℂ) • loweringEnvelopingCocycle i w A := by
  rw [loweringEnvelopingCocycle_apply, loweringUpper_cartan, map_add, map_smul,
    map_add, map_smul, upperSimpleCoefficient_cartan]
  have hc := shiftedCartanEnveloping_commutator (adjacentCartanDiagonal i) 0 (loweringUpper i A)
  simp only [zero_smul, add_zero] at hc
  rw [← hc]
  simp only [loweringEnvelopingCocycle_apply, mul_sub, sub_mul,
    smul_mul_assoc, mul_smul_comm, mul_add, add_mul, mul_one, one_mul,
    smul_sub, smul_add, smul_smul]
  module

end
end Schubert.RS.Representation
