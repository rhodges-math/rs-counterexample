import Schubert.RS.Representation.TypeA
import Mathlib.LinearAlgebra.Pi

namespace Schubert.RS.Representation

noncomputable section

/-- Reading the strictly upper entries is a genuine linear coordinate map. -/
def rootCoordinates (n : ℕ) : upperNilpotent n ≃ₗ[ℂ] (PositiveRoot n → ℂ) where
  toFun A r := A.val r.val.1 r.val.2
  invFun c := ⟨fun i j => if h : i < j then c ⟨(i, j), h⟩ else 0, by
    intro i j hij
    simp [hij]⟩
  left_inv A := by
    apply Subtype.ext
    funext i j
    dsimp
    split_ifs with h
    · rfl
    · exact (A.property i j h).symm
  right_inv c := by
    funext r
    simp [r.property]
  map_add' A B := rfl
  map_smul' c A := rfl

/-- The positive matrix units form the actual vector-space basis of n_+. -/
def rootBasis (n : ℕ) : Module.Basis (PositiveRoot n) ℂ (upperNilpotent n) :=
  (Pi.basisFun ℂ (PositiveRoot n)).map (rootCoordinates n).symm

theorem rootBasis_apply (n : ℕ) (r : PositiveRoot n) : rootBasis n r = rootVector r := by
  apply Subtype.ext
  funext i j
  by_cases hij : i < j
  · simp [rootBasis, rootCoordinates, rootVector, hij, Matrix.single_apply,
      Pi.single_apply, Subtype.ext_iff, Prod.ext_iff, eq_comm]
  · have hne : ¬ (r.val.1 = i ∧ r.val.2 = j) := by
      rintro ⟨hi, hj⟩
      exact hij (hi ▸ hj ▸ r.property)
    simp [rootBasis, rootCoordinates, rootVector, hij, Matrix.single_apply, hne]

end
end Schubert.RS.Representation
