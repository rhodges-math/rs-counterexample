import Schubert.RS.Representation.TypeA

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators
attribute [local instance 100] LieRing.ofAssociativeRing

/-- Commutation with the diagonal matrix with entries h. -/
def cartanMatrix {n : ℕ} (h : Fin n → ℂ) : Square n →ₗ[ℂ] Square n where
  toFun A i j := (h i-h j)*A i j
  map_add' A B := by ext i j; exact mul_add _ _ _
  map_smul' c A := by ext i j; change _*(c*_)=c*(_*_); ring

theorem cartanMatrix_mul {n : ℕ} (h : Fin n → ℂ) (A B : Square n) :
    cartanMatrix h (A*B) = cartanMatrix h A * B + A * cartanMatrix h B := by
  ext i j
  change (h i-h j)*(∑ k, A i k*B k j) =
    (∑ k, ((h i-h k)*A i k)*B k j) + (∑ k, A i k*((h k-h j)*B k j))
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

def cartanUpper {n : ℕ} (h : Fin n → ℂ) : upperNilpotent n →ₗ[ℂ] upperNilpotent n where
  toFun A := ⟨cartanMatrix h A.val, by
    intro i j hij
    change (h i-h j)*A.val i j=0
    rw [A.property i j hij, mul_zero]⟩
  map_add' A B := Subtype.ext ((cartanMatrix h).map_add A.val B.val)
  map_smul' c A := Subtype.ext ((cartanMatrix h).map_smul c A.val)

theorem cartanUpper_lie {n : ℕ} (h : Fin n → ℂ) (A B : upperNilpotent n) :
    cartanUpper h ⁅A,B⁆ = ⁅cartanUpper h A,B⁆ + ⁅A,cartanUpper h B⁆ := by
  apply Subtype.ext
  change cartanMatrix h (A.val*B.val-B.val*A.val) =
    (cartanMatrix h A.val*B.val-B.val*cartanMatrix h A.val) +
      (A.val*cartanMatrix h B.val-cartanMatrix h B.val*A.val)
  rw [map_sub, cartanMatrix_mul, cartanMatrix_mul]
  abel

theorem cartanUpper_root {n : ℕ} (h : Fin n → ℂ) (r : PositiveRoot n) :
    cartanUpper h (rootVector r) = (h r.val.1-h r.val.2) • rootVector r := by
  apply Subtype.ext
  ext i j
  change (h i-h j)*Matrix.single r.val.1 r.val.2 (1 : ℂ) i j =
    (h r.val.1-h r.val.2)*Matrix.single r.val.1 r.val.2 (1 : ℂ) i j
  simp only [Matrix.single_apply]
  split_ifs with hij
  · rcases hij with ⟨rfl,rfl⟩
    rfl
  · simp

end
end Schubert.RS.Representation
