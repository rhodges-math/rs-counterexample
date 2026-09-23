import Schubert.RS.Representation.FlagWeights

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators
attribute [local instance 100] LieRing.ofAssociativeRing

theorem rowDerivation_torus {n : ℕ} (t : DiagonalTorus n) (A : Square n)
    (p : MatrixPolynomial n) :
    rowAction (Matrix.diagonal fun i => (t i : ℂ)) (rowDerivation A p) =
      rowDerivation (torusMatrix t A) (rowAction (Matrix.diagonal fun i => (t i : ℂ)) p) := by
  have hx (rc : Fin n × Fin n) :
      rowAction (Matrix.diagonal fun i => (t i : ℂ)) (rowDerivation A (MvPolynomial.X rc)) =
      rowDerivation (torusMatrix t A)
        (rowAction (Matrix.diagonal fun i => (t i : ℂ)) (MvPolynomial.X rc)) := by
    obtain ⟨r,c⟩ := rc
    have ht (i j : Fin n) : rowAction (Matrix.diagonal fun i => (t i : ℂ))
        (MvPolynomial.X (i,j)) = (t i : ℂ) • MvPolynomial.X (i,j) := polynomialTorus_X t i j
    simp only [rowDerivation_X, ht, map_sum, map_smul, Derivation.map_smul_of_tower,
      Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    simp [torusMatrix, rootScalar, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    field_simp
  induction p using MvPolynomial.induction_on with
  | C c => simp [rowAction]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p rc hp =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hp, hx]

def polynomialTorusEquiv {n : ℕ} (t : DiagonalTorus n) : MatrixPolynomial n ≃ₗ[ℂ] MatrixPolynomial n where
  toLinearMap := polynomialTorus n t
  invFun := polynomialTorus n t⁻¹
  left_inv p := by
    change polynomialTorus n t⁻¹ (polynomialTorus n t p) = p
    have h := congrArg (fun f : Module.End ℂ (MatrixPolynomial n) => f p)
      ((polynomialTorus n).map_mul t⁻¹ t)
    simpa only [inv_mul_cancel, map_one, Module.End.one_apply, Module.End.mul_apply] using h.symm
  right_inv p := by
    change polynomialTorus n t (polynomialTorus n t⁻¹ p) = p
    have h := congrArg (fun f : Module.End ℂ (MatrixPolynomial n) => f p)
      ((polynomialTorus n).map_mul t t⁻¹)
    simpa only [mul_inv_cancel, map_one, Module.End.one_apply, Module.End.mul_apply] using h.symm

theorem polynomialEnveloping_torus_conjugate {n : ℕ} (t : DiagonalTorus n) :
    ((polynomialTorusEquiv t).conjAlgEquiv ℂ).toAlgHom.comp (polynomialEnveloping n) =
      (polynomialEnveloping n).comp (torusEnveloping t) := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro A
  apply LinearMap.ext
  intro p
  change polynomialTorus n t
    (polynomialEnveloping n (UniversalEnvelopingAlgebra.ι ℂ A) (polynomialTorus n t⁻¹ p)) =
    polynomialEnveloping n (torusEnveloping t (UniversalEnvelopingAlgebra.ι ℂ A)) p
  have hi (B : upperNilpotent n) : polynomialEnveloping n (UniversalEnvelopingAlgebra.ι ℂ B) =
      (rowDerivation B.val).toLinearMap := by
    change UniversalEnvelopingAlgebra.lift ℂ (polynomialUpperLie n) (UniversalEnvelopingAlgebra.ι ℂ B) = _
    rw [UniversalEnvelopingAlgebra.lift_ι_apply]
    rfl
  rw [hi]
  change rowAction (Matrix.diagonal fun i => (t i : ℂ))
    (rowDerivation A.val (polynomialTorus n t⁻¹ p)) = _
  rw [rowDerivation_torus]
  have hp : rowAction (Matrix.diagonal fun i => (t i : ℂ)) (polynomialTorus n t⁻¹ p) = p :=
    (polynomialTorusEquiv t).apply_symm_apply p
  rw [hp]
  change rowDerivation (torusMatrix t A.val) p =
    polynomialEnveloping n (UniversalEnvelopingAlgebra.lift ℂ
      ((UniversalEnvelopingAlgebra.ι ℂ).comp (torusLie t)) (UniversalEnvelopingAlgebra.ι ℂ A)) p
  rw [UniversalEnvelopingAlgebra.lift_ι_apply]
  change rowDerivation (torusMatrix t A.val) p =
    polynomialEnveloping n (UniversalEnvelopingAlgebra.ι ℂ (torusLie t A)) p
  rw [hi]
  rfl

/-- Torus covariance for the actual U(n_+) action on the polynomial ambient. -/
theorem polynomialEnveloping_torus {n : ℕ} (t : DiagonalTorus n) (a : Enveloping n)
    (p : MatrixPolynomial n) :
    polynomialTorus n t (polynomialEnveloping n a p) =
      polynomialEnveloping n (torusEnveloping t a) (polynomialTorus n t p) := by
  have h := AlgHom.congr_fun (polynomialEnveloping_torus_conjugate t) a
  have hv := congrArg (fun f : Module.End ℂ (MatrixPolynomial n) => f (polynomialTorus n t p)) h
  change polynomialTorus n t (polynomialEnveloping n a
    ((polynomialTorusEquiv t).symm (polynomialTorusEquiv t p))) = _ at hv
  rw [(polynomialTorusEquiv t).symm_apply_apply] at hv
  exact hv

end
end Schubert.RS.Representation
