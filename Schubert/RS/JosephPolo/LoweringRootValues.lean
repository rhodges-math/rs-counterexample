import Schubert.RS.JosephPolo.LoweringEnveloping
import Schubert.RS.JosephPolo.RootLoweringRelations

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
set_option maxHeartbeats 1200000

theorem upperSimpleCoefficient_simple {n : ℕ} (i : AdjacentPosition n) :
    upperSimpleCoefficient i (rootVector (adjacentPositiveRoot i))=1 := by
  rw [upperSimpleCoefficient_apply]
  change Matrix.single i.left i.right (1 : ℂ) i.left i.right=1
  simp

theorem upperSimpleCoefficient_root_ne {n : ℕ} (i : AdjacentPosition n)
    (r : PositiveRoot n) (hr : r≠adjacentPositiveRoot i) :
    upperSimpleCoefficient i (rootVector r)=0 := by
  rw [upperSimpleCoefficient_apply]
  change Matrix.single r.val.1 r.val.2 (1 : ℂ) i.left i.right=0
  have hn : ¬ (r.val.1=i.left ∧ r.val.2=i.right) := by
    rintro ⟨ha,hb⟩
    exact hr (Subtype.ext (Prod.ext ha hb))
  simp [Matrix.single_apply, hn]

theorem loweringUpper_simple {n : ℕ} (i : AdjacentPosition n) :
    loweringUpper i (rootVector (adjacentPositiveRoot i))=0 := by
  apply Subtype.ext
  change Matrix.single i.right i.left (1 : ℂ) * Matrix.single i.left i.right 1 -
    Matrix.single i.left i.right 1 * Matrix.single i.right i.left 1 +
    upperSimpleCoefficient i (rootVector (adjacentPositiveRoot i)) • adjacentCartanMatrix i=0
  rw [upperSimpleCoefficient_simple, one_smul,
    Matrix.single_mul_single_same, Matrix.single_mul_single_same, one_mul]
  unfold adjacentCartanMatrix
  abel

theorem loweringUpper_incoming {n : ℕ} (i : AdjacentPosition n) (a : Fin n) (ha : a < i.left) :
    loweringUpper i (rootVector ⟨(a,i.right),ha.trans i.left_lt_right⟩) =
      -rootVector ⟨(a,i.left),ha⟩ := by
  have hr : (⟨(a,i.right),ha.trans i.left_lt_right⟩ : PositiveRoot n) ≠ adjacentPositiveRoot i := by
    intro h
    exact (ne_of_lt ha) (congrArg (fun r : PositiveRoot n => r.val.1) h)
  apply Subtype.ext
  change Matrix.single i.right i.left (1 : ℂ) * Matrix.single a i.right 1 -
    Matrix.single a i.right 1 * Matrix.single i.right i.left 1 +
    upperSimpleCoefficient i (rootVector ⟨(a,i.right),ha.trans i.left_lt_right⟩) • adjacentCartanMatrix i =
    -Matrix.single a i.left 1
  rw [upperSimpleCoefficient_root_ne i _ hr, zero_smul, add_zero,
    Matrix.single_mul_single_of_ne (1 : ℂ) i.right i.left a (ne_of_gt ha),
    Matrix.single_mul_single_same, one_mul, zero_sub]

theorem loweringUpper_outgoing {n : ℕ} (i : AdjacentPosition n) (b : Fin n) (hb : i.right < b) :
    loweringUpper i (rootVector ⟨(i.left,b),i.left_lt_right.trans hb⟩) =
      rootVector ⟨(i.right,b),hb⟩ := by
  have hr : (⟨(i.left,b),i.left_lt_right.trans hb⟩ : PositiveRoot n) ≠ adjacentPositiveRoot i := by
    intro h
    exact (ne_of_gt hb) (congrArg (fun r : PositiveRoot n => r.val.2) h)
  apply Subtype.ext
  change Matrix.single i.right i.left (1 : ℂ) * Matrix.single i.left b 1 -
    Matrix.single i.left b 1 * Matrix.single i.right i.left 1 +
    upperSimpleCoefficient i (rootVector ⟨(i.left,b),i.left_lt_right.trans hb⟩) • adjacentCartanMatrix i =
    Matrix.single i.right b 1
  rw [upperSimpleCoefficient_root_ne i _ hr, zero_smul, add_zero,
    Matrix.single_mul_single_same, one_mul,
    Matrix.single_mul_single_of_ne (1 : ℂ) i.left b i.right (ne_of_gt hb), sub_zero]

theorem loweringUpper_other {n : ℕ} (i : AdjacentPosition n) (r : PositiveRoot n)
    (ha : r.val.1≠i.left) (hb : r.val.2≠i.right) : loweringUpper i (rootVector r)=0 := by
  have hr : r≠adjacentPositiveRoot i := fun h => ha (congrArg (fun s : PositiveRoot n => s.val.1) h)
  apply Subtype.ext
  change Matrix.single i.right i.left (1 : ℂ) * Matrix.single r.val.1 r.val.2 1 -
    Matrix.single r.val.1 r.val.2 1 * Matrix.single i.right i.left 1 +
    upperSimpleCoefficient i (rootVector r) • adjacentCartanMatrix i=0
  rw [upperSimpleCoefficient_root_ne i r hr, zero_smul,
    Matrix.single_mul_single_of_ne (1 : ℂ) i.right i.left r.val.1 (Ne.symm ha),
    Matrix.single_mul_single_of_ne (1 : ℂ) r.val.1 r.val.2 i.right hb]
  simp

theorem adjacentCartan_simple_weight {n : ℕ} (i : AdjacentPosition n) :
    adjacentCartanDiagonal i i.left-adjacentCartanDiagonal i i.right=2 := by
  simp [adjacentCartanDiagonal, i.left_ne_right, Ne.symm i.left_ne_right]
  norm_num

end
end Schubert.RS.Representation
