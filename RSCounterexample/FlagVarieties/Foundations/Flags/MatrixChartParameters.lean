import RSCounterexample.FlagVarieties.Foundations.Flags.MatrixChartFunctor
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Polynomial parameters for the normalized matrix chart

Matrices are represented by evaluations of a polynomial ring with one
variable per entry. Their normalized Grassmannian points form a
natural transformation, injective at every algebra. This is the affine
parameter family of the chart; the regular overlap maps between such charts
are `Schemes/MatrixOverlapMap.lean`.
-/

namespace FlagVarieties.Foundations.QuotientCharts

open CategoryTheory TensorProduct

attribute [local ext high] ConcreteCategory.hom_ext

universe u

variable (R : Type u) [CommRing R] (d c : ℕ)

/-- Polynomial evaluations are exactly the matrix parameters. -/
noncomputable def matrixEvaluationEquiv (A : Type*) [CommRing A] [Algebra R A] :
    (MvPolynomial (Fin d × Fin c) R →ₐ[R] A) ≃ Matrix (Fin d) (Fin c) A where
  toFun φ i j := φ (MvPolynomial.X (i, j))
  invFun C := MvPolynomial.aeval (fun ij => C ij.1 ij.2)
  left_inv φ := by
    ext ij
    simp
  right_inv C := by
    ext i j
    simp

@[simp] theorem matrixEvaluationEquiv_apply (A : Type*) [CommRing A] [Algebra R A]
    (φ : MvPolynomial (Fin d × Fin c) R →ₐ[R] A) (i : Fin d) (j : Fin c) :
    matrixEvaluationEquiv R d c A φ i j = φ (MvPolynomial.X (i, j)) := rfl

theorem matrixEvaluationEquiv_comp {A B : Type*} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B)
    (φ : MvPolynomial (Fin d × Fin c) R →ₐ[R] A) :
    matrixEvaluationEquiv R d c B (f.comp φ) = (matrixEvaluationEquiv R d c A φ).map f := rfl

/-- Entrywise scalar extension defines the matrix parameter functor. -/
def matrixParameterFunctor : CommAlgCat.{u, u} R ⥤ Type u where
  obj A := Matrix (Fin d) (Fin c) A
  map f := ↾fun C => C.map f.hom
  map_id A := by ext C i j; rfl
  map_comp f g := by ext C i j; rfl

/-- The Grassmannian family defined by normalized matrix kernels. -/
noncomputable def matrixParameterToGrassmannian :
    matrixParameterFunctor R d c ⟶
      Module.Grassmannian.functor (R := R) (M := (Fin d → R) × (Fin c → R)) d where
  app A := ↾fun C => matrixFunctorPoint R C
  naturality A B f := by
    ext C : 1
    exact (matrixFunctorPoint_map R f.hom C).symm

/-- The family does not identify two different matrix parameters. -/
theorem matrixFunctorPoint_injective {A : Type*} [CommRing A] [Algebra R A] :
    Function.Injective (matrixFunctorPoint R (d := d) (c := c) (A := A)) := by
  intro C D h
  have ht := (grassmannianTransportEquiv (matrixChartTensorEquiv R A d c).symm).injective h
  apply matrixGrassmannianChartEquiv.injective
  exact Subtype.ext ht

theorem matrixParameterToGrassmannian_app_injective (A : CommAlgCat.{u, u} R) :
    Function.Injective ((matrixParameterToGrassmannian R d c).app A) :=
  matrixFunctorPoint_injective R d c

end FlagVarieties.Foundations.QuotientCharts
