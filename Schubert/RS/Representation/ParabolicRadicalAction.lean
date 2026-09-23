import Schubert.RS.Representation.ParabolicRadicalLie
import Schubert.RS.Representation.RankOneActionExtension

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ} (i : AdjacentPosition n) (S : Submodule ℂ (MatrixPolynomial n))
  (hS : ∀ r : RadicalRoot i, ∀ p∈S, matrixUnitDerivation r.val.val.1 r.val.val.2 p∈S)

/-- The actual restricted polynomial radical action, bundled bilinearly. -/
def radicalPolynomialAction : (radicalEndLie i ⊗[ℂ] S) →ₗ[ℂ] S :=
  letI := radicalPolynomialLieRingModule i S hS
  letI := radicalPolynomialLieModule i S hS
  (LieModule.toModuleHom ℂ (radicalEndLie i) S).toLinearMap

theorem radicalPolynomialAction_tmul_val (r : radicalEndLie i) (p : S) :
    (radicalPolynomialAction i S hS (r ⊗ₜ[ℂ] p) : MatrixPolynomial n) = r.val p.val := by
  letI := radicalPolynomialLieRingModule i S hS
  letI := radicalPolynomialLieModule i S hS
  change ((LieModule.toModuleHom ℂ (radicalEndLie i) S (r ⊗ₜ[ℂ] p) : S) : MatrixPolynomial n) = _
  rw [LieModule.toModuleHom_apply]
  rfl

theorem radicalPolynomialAction_root (r : RadicalRoot i) (p : S) :
    (radicalPolynomialAction i S hS (radicalEndRoot i r ⊗ₜ[ℂ] p) : MatrixPolynomial n) =
      matrixUnitDerivation r.val.val.1 r.val.val.2 p.val :=
  radicalPolynomialAction_tmul_val i S hS (radicalEndRoot i r) p

/-- Equivariance is inherited from the actual polynomial commutator, for
any restricted Levi operator on the source. -/
theorem radicalPolynomialAction_intertwines
    (a : (polynomialSl2Triple i.left i.right i.left_ne_right).toLieSubalgebra ℂ)
    (D : Module.End ℂ S) (hD : ∀ p : S, (D p : MatrixPolynomial n) = a.val p.val)
    (z : radicalEndLie i ⊗[ℂ] S) :
    radicalPolynomialAction i S hS (tensorBorelOperator a D z) = D (radicalPolynomialAction i S hS z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r p =>
      rw [tensorBorelOperator_tmul,map_add]
      apply Subtype.ext
      simp only [Submodule.coe_add,radicalPolynomialAction_tmul_val,hD,
        radicalEndLie_levi_action_val]
      change (a.val (r.val p.val) - r.val (a.val p.val)) + r.val (a.val p.val) = a.val (r.val p.val)
      exact sub_add_cancel _ _
  | add z w hz hw => simp only [map_add,hz,hw]

/-- The source radical action satisfies the Lie-action identity as an
identity of actual restricted polynomial operators. -/
theorem radicalPolynomialAction_jacobi (r s : radicalEndLie i) (p : S) :
    radicalPolynomialAction i S hS (⁅r,s⁆ ⊗ₜ[ℂ] p) =
      radicalPolynomialAction i S hS (r ⊗ₜ[ℂ] radicalPolynomialAction i S hS (s ⊗ₜ[ℂ] p)) -
      radicalPolynomialAction i S hS (s ⊗ₜ[ℂ] radicalPolynomialAction i S hS (r ⊗ₜ[ℂ] p)) := by
  apply Subtype.ext
  simp only [Submodule.coe_sub,radicalPolynomialAction_tmul_val]
  rfl

end
end Schubert.RS.Representation
