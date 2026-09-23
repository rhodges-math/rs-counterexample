import Schubert.RS.JosephPolo.CartanLie
import Schubert.RS.Representation.UpperRadicalDecomposition

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1200000

def adjacentCartanDiagonal {n : ℕ} (i : AdjacentPosition n) (j : Fin n) : ℂ :=
  (if j=i.left then 1 else 0) - (if j=i.right then 1 else 0)

def adjacentCartanMatrix {n : ℕ} (i : AdjacentPosition n) : Square n :=
  Matrix.single i.left i.left 1 - Matrix.single i.right i.right 1

theorem adjacentCartanMatrix_eq_diagonal {n : ℕ} (i : AdjacentPosition n) :
    adjacentCartanMatrix i = Matrix.diagonal (adjacentCartanDiagonal i) := by
  ext a b
  by_cases hab : a=b
  · subst b
    simp [adjacentCartanMatrix, adjacentCartanDiagonal, Matrix.single_apply, eq_comm]
  · have hl : ¬ (i.left=a ∧ i.left=b) := by
      rintro ⟨ha,hb⟩
      exact hab (ha.symm.trans hb)
    have hr : ¬ (i.right=a ∧ i.right=b) := by
      rintro ⟨ha,hb⟩
      exact hab (ha.symm.trans hb)
    simp [adjacentCartanMatrix, Matrix.single_apply, hl, hr, hab]

theorem cartanMatrix_eq_commutator {n : ℕ} (h : Fin n → ℂ) (A : Square n) :
    cartanMatrix h A = Matrix.diagonal h * A - A * Matrix.diagonal h := by
  ext a b
  change (h a-h b)*A a b = (Matrix.diagonal h*A) a b-(A*Matrix.diagonal h) a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

def loweringRemainderMatrix {n : ℕ} (i : AdjacentPosition n) : upperNilpotent n →ₗ[ℂ] Square n where
  toFun A := Matrix.single i.right i.left 1 * A.val - A.val * Matrix.single i.right i.left 1 +
    upperSimpleCoefficient i A • adjacentCartanMatrix i
  map_add' A B := by
    change Matrix.single i.right i.left 1 * (A.val+B.val) -
      (A.val+B.val)*Matrix.single i.right i.left 1 +
      upperSimpleCoefficient i (A+B) • adjacentCartanMatrix i = _
    simp only [map_add, mul_add, add_mul, add_smul]
    abel
  map_smul' c A := by
    change Matrix.single i.right i.left 1 * (c • A.val) -
      (c • A.val)*Matrix.single i.right i.left 1 +
      upperSimpleCoefficient i (c • A) • adjacentCartanMatrix i = _
    simp only [map_smul, RingHom.id_apply,
      mul_smul_comm, smul_mul_assoc, smul_smul, smul_add, smul_sub]
    rfl

theorem loweringRemainderMatrix_upper {n : ℕ} (i : AdjacentPosition n) (A : upperNilpotent n) :
    loweringRemainderMatrix i A ∈ upperNilpotent n := by
  intro a b hab
  change ((Matrix.single i.right i.left (1 : ℂ)*A.val) a b -
    (A.val*Matrix.single i.right i.left (1 : ℂ)) a b) +
    upperSimpleCoefficient i A * (adjacentCartanMatrix i) a b=0
  rw [upperSimpleCoefficient_apply]
  by_cases ha : a=i.right
  · subst a
    rw [Matrix.single_mul_apply_same]
    by_cases hb : b=i.left
    · subst b
      rw [Matrix.mul_single_apply_same]
      have hll := A.property i.left i.left (lt_irrefl _)
      have hrr := A.property i.right i.right (lt_irrefl _)
      simp [hll, hrr, adjacentCartanMatrix, Matrix.single_apply, i.left_ne_right, Ne.symm i.left_ne_right]
    · rw [Matrix.mul_single_apply_of_ne (1 : ℂ) i.right i.left i.right b hb A.val]
      by_cases hbr : b=i.right
      · subst b
        simp [adjacentCartanMatrix, Matrix.single_apply, i.left_ne_right, Ne.symm i.left_ne_right]
      · have hnot : ¬ i.left < b := by
          have hv := i.right_val
          have hn : b.val≠i.right.val := fun h => hbr (Fin.ext h)
          change ¬ i.right.val < b.val at hab
          change ¬ i.left.val < b.val
          omega
        rw [A.property i.left b hnot]
        simp [adjacentCartanMatrix, Matrix.single_apply, i.left_ne_right, Ne.symm hbr]
  · rw [Matrix.single_mul_apply_of_ne (1 : ℂ) i.right i.left a b ha A.val]
    by_cases hb : b=i.left
    · subst b
      rw [Matrix.mul_single_apply_same]
      by_cases hal : a=i.left
      · subst a
        simp [adjacentCartanMatrix, Matrix.single_apply, i.left_ne_right, Ne.symm i.left_ne_right]
      · have hnot : ¬ a < i.right := by
          have hv := i.right_val
          have hn : a.val≠i.left.val := fun h => hal (Fin.ext h)
          change ¬ a.val < i.left.val at hab
          change ¬ a.val < i.right.val
          omega
        rw [A.property a i.right hnot]
        simp [adjacentCartanMatrix, Matrix.single_apply, Ne.symm ha, Ne.symm hal]
    · rw [Matrix.mul_single_apply_of_ne (1 : ℂ) i.right i.left a b hb A.val]
      simp [adjacentCartanMatrix, Matrix.single_apply, Ne.symm ha, Ne.symm hb]

def loweringUpper {n : ℕ} (i : AdjacentPosition n) : upperNilpotent n →ₗ[ℂ] upperNilpotent n where
  toFun A := ⟨loweringRemainderMatrix i A, loweringRemainderMatrix_upper i A⟩
  map_add' A B := Subtype.ext ((loweringRemainderMatrix i).map_add A B)
  map_smul' c A := Subtype.ext ((loweringRemainderMatrix i).map_smul c A)

theorem loweringUpper_lie {n : ℕ} (i : AdjacentPosition n) (A B : upperNilpotent n) :
    loweringUpper i ⁅A,B⁆ = ⁅loweringUpper i A,B⁆ + ⁅A,loweringUpper i B⁆ -
      upperSimpleCoefficient i A • cartanUpper (adjacentCartanDiagonal i) B +
      upperSimpleCoefficient i B • cartanUpper (adjacentCartanDiagonal i) A := by
  apply Subtype.ext
  change loweringRemainderMatrix i ⁅A,B⁆ =
    (loweringRemainderMatrix i A*B.val-B.val*loweringRemainderMatrix i A) +
      (A.val*loweringRemainderMatrix i B-loweringRemainderMatrix i B*A.val) -
      upperSimpleCoefficient i A • cartanMatrix (adjacentCartanDiagonal i) B.val +
      upperSimpleCoefficient i B • cartanMatrix (adjacentCartanDiagonal i) A.val
  rw [cartanMatrix_eq_commutator, cartanMatrix_eq_commutator, ← adjacentCartanMatrix_eq_diagonal]
  change (Matrix.single i.right i.left 1 * (A.val*B.val-B.val*A.val) -
    (A.val*B.val-B.val*A.val) * Matrix.single i.right i.left 1 +
      upperSimpleCoefficient i ⁅A,B⁆ • adjacentCartanMatrix i) = _
  rw [upperSimpleCoefficient_bracket, zero_smul, add_zero]
  simp only [loweringRemainderMatrix, LinearMap.coe_mk, AddHom.coe_mk,
    mul_sub, sub_mul, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_sub, mul_assoc]
  module

end
end Schubert.RS.Representation
