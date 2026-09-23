import Schubert.RS.Representation.FlagCyclic

namespace Schubert.RS.Representation
noncomputable section

/-- Covariant convention: the j-th standard vector is sent to e_(w j). -/
def rowPermutationMatrix {n : ℕ} (w : Equiv.Perm (Fin n)) : Square n :=
  fun i j => if i = w j then 1 else 0

theorem rowPermutationMatrix_one (n : ℕ) : rowPermutationMatrix (1 : Equiv.Perm (Fin n)) = 1 := by
  apply Matrix.ext
  intro i j
  simp [rowPermutationMatrix, Matrix.one_apply]
  rfl

theorem rowPermutationMatrix_mul {n : ℕ} (v w : Equiv.Perm (Fin n)) :
    rowPermutationMatrix (v*w) = rowPermutationMatrix v * rowPermutationMatrix w := by
  apply Matrix.ext
  intro i j
  simp [rowPermutationMatrix, Matrix.mul_apply, mul_ite, Equiv.Perm.mul_apply]
  rfl

def rowPermutationUnit {n : ℕ} (w : Equiv.Perm (Fin n)) : (Square n)ˣ where
  val := rowPermutationMatrix w
  inv := rowPermutationMatrix w⁻¹
  val_inv := by rw [← rowPermutationMatrix_mul, mul_inv_cancel, rowPermutationMatrix_one]
  inv_val := by rw [← rowPermutationMatrix_mul, inv_mul_cancel, rowPermutationMatrix_one]

theorem rowAction_permutation {n : ℕ} (w : Equiv.Perm (Fin n)) :
    rowAction (rowPermutationMatrix w) = rowRename w := by
  apply MvPolynomial.algHom_ext
  rintro ⟨r,c⟩
  rw [rowAction_X]
  simp [rowPermutationMatrix, rowRename, ite_smul]

/-- The extremal candidate is literally the action of a Weyl permutation
matrix on the highest flag vector, in the concrete GL_n representation. -/
theorem polynomialGL_extremal {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n)) :
    polynomialGL n (rowPermutationUnit w) (highestFlag m) = extremalFlag m w := by
  change rowAction (rowPermutationMatrix w) (highestFlag m) = _
  rw [rowAction_permutation]
  rfl

theorem extremalFlag_mem_orbitSpan {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n)) :
    extremalFlag m w ∈ flagOrbitSpan m := by
  rw [← polynomialGL_extremal m w]
  exact Submodule.subset_span ⟨rowPermutationUnit w, rfl⟩

end
end Schubert.RS.Representation
