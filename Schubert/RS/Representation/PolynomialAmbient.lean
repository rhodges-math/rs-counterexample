import Schubert.RS.Representation.Torus
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators
attribute [local instance 100] LieRing.ofAssociativeRing

/-- A concrete polynomial representation containing the flag-minor Schur model.
The first variable index transforms as the standard GL_n representation. -/
abbrev MatrixPolynomial (n : ℕ) := MvPolynomial (Fin n × Fin n) ℂ

def rowAction {n : ℕ} (g : Square n) : MatrixPolynomial n →ₐ[ℂ] MatrixPolynomial n :=
  MvPolynomial.aeval (fun rc => ∑ i, g i rc.1 • MvPolynomial.X (i, rc.2))

@[simp] theorem rowAction_X {n : ℕ} (g : Square n) (r c : Fin n) :
    rowAction g (MvPolynomial.X (r,c)) = ∑ i, g i r • MvPolynomial.X (i,c) :=
  MvPolynomial.aeval_X _ _

theorem rowAction_one (n : ℕ) : rowAction (1 : Square n) = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  rintro ⟨r,c⟩
  simp [rowAction, Matrix.one_apply]

theorem rowAction_mul {n : ℕ} (g h : Square n) :
    rowAction (g * h) = (rowAction g).comp (rowAction h) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨r,c⟩
  simp only [rowAction_X, AlgHom.comp_apply, map_sum, map_smul,
    Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_comm]

/-- The ordinary GL_n(C) representation, using units of the matrix algebra. -/
def polynomialGL (n : ℕ) : (Square n)ˣ →* Module.End ℂ (MatrixPolynomial n) where
  toFun g := (rowAction g.val).toLinearMap
  map_one' := by apply LinearMap.ext; intro p; exact AlgHom.congr_fun (rowAction_one n) p
  map_mul' g h := by apply LinearMap.ext; intro p; exact AlgHom.congr_fun (rowAction_mul g.val h.val) p

/-- The differentiated action is a derivation with the same matrix coefficients. -/
def rowDerivation {n : ℕ} (A : Square n) : Derivation ℂ (MatrixPolynomial n) (MatrixPolynomial n) :=
  MvPolynomial.mkDerivation ℂ (fun rc => ∑ i, A i rc.1 • MvPolynomial.X (i, rc.2))

@[simp] theorem rowDerivation_X {n : ℕ} (A : Square n) (r c : Fin n) :
    rowDerivation A (MvPolynomial.X (r,c)) = ∑ i, A i r • MvPolynomial.X (i,c) :=
  MvPolynomial.mkDerivation_X _ _ _

def rowDerivationLinear (n : ℕ) : Square n →ₗ[ℂ] Derivation ℂ (MatrixPolynomial n) (MatrixPolynomial n) where
  toFun := rowDerivation
  map_add' A B := by
    apply MvPolynomial.derivation_ext
    rintro ⟨r,s⟩
    simp [rowDerivation_X, add_smul, Finset.sum_add_distrib]
  map_smul' c A := by
    apply MvPolynomial.derivation_ext
    rintro ⟨r,s⟩
    simp [rowDerivation_X, mul_smul, Finset.smul_sum]

theorem rowDerivation_bracket {n : ℕ} (A B : Square n) :
    rowDerivation ⁅A, B⁆ = ⁅rowDerivation A, rowDerivation B⁆ := by
  apply MvPolynomial.derivation_ext
  rintro ⟨r,c⟩
  change rowDerivation (A*B-B*A) (MvPolynomial.X (r,c)) =
    rowDerivation A (rowDerivation B (MvPolynomial.X (r,c))) -
      rowDerivation B (rowDerivation A (MvPolynomial.X (r,c)))
  simp only [rowDerivation_X, Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib,
    Matrix.mul_apply, Finset.sum_smul, map_sum, Derivation.map_smul_of_tower,
    Finset.smul_sum, smul_smul]
  congr 1 <;> rw [Finset.sum_comm] <;>
    apply Finset.sum_congr rfl <;> intro i hi <;>
    apply Finset.sum_congr rfl <;> intro j hj <;> rw [mul_comm]

/-- The concrete gl_n action by polynomial derivations. -/
def polynomialLie (n : ℕ) : Square n →ₗ⁅ℂ⁆ Module.End ℂ (MatrixPolynomial n) where
  toLinearMap :=
    { toFun := fun A => (rowDerivation A).toLinearMap
      map_add' := fun A B => congrArg Derivation.toLinearMap ((rowDerivationLinear n).map_add A B)
      map_smul' := fun c A => congrArg Derivation.toLinearMap ((rowDerivationLinear n).map_smul c A) }
  map_lie' {A B} := congrArg Derivation.toLinearMap (rowDerivation_bracket A B)

def polynomialUpperLie (n : ℕ) : upperNilpotent n →ₗ⁅ℂ⁆ Module.End ℂ (MatrixPolynomial n) :=
  (polynomialLie n).comp (upperNilpotent n).incl

/-- The actual U(n_+) action on matrix polynomials, independent of any quotient. -/
def polynomialEnveloping (n : ℕ) : Enveloping n →ₐ[ℂ] Module.End ℂ (MatrixPolynomial n) :=
  UniversalEnvelopingAlgebra.lift ℂ (polynomialUpperLie n)

theorem polynomialEnveloping_root {n : ℕ} (r : PositiveRoot n) :
    polynomialEnveloping n (rootOperator r) = (rowDerivation (rootVector r).val).toLinearMap := by
  change UniversalEnvelopingAlgebra.lift ℂ (polynomialUpperLie n)
    (UniversalEnvelopingAlgebra.ι ℂ (rootVector r)) = _
  rw [UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

end
end Schubert.RS.Representation
