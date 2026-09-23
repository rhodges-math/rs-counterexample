import Schubert.RS.Representation.FlagCyclic

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators

def flagMinorScalar {n : ℕ} (k : Fin n) (t : DiagonalTorus n) : ℂ :=
  ∏ i : Fin (k.val+1), (t (prefixIndex k i) : ℂ)

theorem flagMinor_diagonal {n : ℕ} (k : Fin n) (t : DiagonalTorus n) :
    polynomialTorus n t (flagMinor k) = flagMinorScalar k t • flagMinor k := by
  let M : Matrix (Fin (k.val+1)) (Fin (k.val+1)) (MatrixPolynomial n) :=
    fun i j => MvPolynomial.X (prefixIndex k i, prefixIndex k j)
  let v : Fin (k.val+1) → MatrixPolynomial n :=
    fun i => MvPolynomial.C (t (prefixIndex k i) : ℂ)
  have hm : (rowAction (Matrix.diagonal fun i => (t i : ℂ))).mapMatrix M =
      Matrix.of (fun i j => v i * M i j) := by
    apply Matrix.ext
    intro i j
    change rowAction (Matrix.diagonal fun i => (t i : ℂ))
      (MvPolynomial.X (prefixIndex k i, prefixIndex k j)) = _
    rw [show rowAction (Matrix.diagonal fun i => (t i : ℂ))
      (MvPolynomial.X (prefixIndex k i, prefixIndex k j)) =
      polynomialTorus n t (MvPolynomial.X (prefixIndex k i, prefixIndex k j)) by rfl]
    rw [polynomialTorus_X]
    exact MvPolynomial.smul_eq_C_mul _ _
  have hp : ∏ i, v i = MvPolynomial.C (flagMinorScalar k t) := by
    simp [v, flagMinorScalar, map_prod]
  change rowAction (Matrix.diagonal fun i => (t i : ℂ)) (Matrix.det M) = _
  rw [AlgHom.map_det, hm, Matrix.det_mul_column, hp, MvPolynomial.C_mul']
  rfl

def highestFlagScalar {n : ℕ} (m : ColumnShape n) (t : DiagonalTorus n) : ℂ :=
  ∏ k, flagMinorScalar k t ^ m k

/-- The diagonal eigenvalue is derived directly from determinant row scaling. -/
theorem highestFlag_diagonal {n : ℕ} (m : ColumnShape n) (t : DiagonalTorus n) :
    polynomialTorus n t (highestFlag m) = highestFlagScalar m t • highestFlag m := by
  change rowAction (Matrix.diagonal fun i => (t i : ℂ)) (∏ k, flagMinor k ^ m k) = _
  rw [map_prod]
  simp only [map_pow]
  have hf (k : Fin n) : rowAction (Matrix.diagonal fun i => (t i : ℂ)) (flagMinor k) =
      flagMinorScalar k t • flagMinor k := flagMinor_diagonal k t
  simp only [hf, smul_pow]
  rw [Finset.prod_smul]
  rfl

end
end Schubert.RS.Representation
