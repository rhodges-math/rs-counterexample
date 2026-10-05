import Schubert.FlagVarieties.Foundations.Flags.GrassmannianTransport
import Schubert.FlagVarieties.Foundations.Flags.MatrixChartBaseChange

/-!
# Normalized matrices in the Grassmannian functor

The ambient space of Mathlib's functor is `A ⊗[R] M`. We transport the
normalized matrix kernel to that space by the canonical coordinate
equivalence, and compare its Grassmannian map with entrywise scalar
extension. The comparison uses the quotient-kernel definition of that map.
-/

namespace FlagVarieties.Foundations.QuotientCharts

open TensorProduct AlgebraTensorModule

universe u w

variable (R : Type u) [CommRing R] {A : Type w} [CommRing A] [Algebra R A]
  {d c : ℕ}

/-- The normalized matrix point in the Grassmannian functor ambient space. -/
noncomputable def matrixFunctorPoint (C : Matrix (Fin d) (Fin c) A) :
    Module.Grassmannian A (A ⊗[R] ((Fin d → R) × (Fin c → R))) d :=
  grassmannianTransport (matrixGrassmannianChartEquiv C).val
    (matrixChartTensorEquiv R A d c).symm

@[simp] theorem matrixFunctorPoint_submodule (C : Matrix (Fin d) (Fin c) A) :
    (matrixFunctorPoint R C).toSubmodule =
      (matrixGrassmannianChartEquiv C).val.toSubmodule.map
        (matrixChartTensorEquiv R A d c).symm.toLinearMap := rfl

section Tower

variable (B : Type w) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- Tensor associativity and coordinate evaluation give the same ambient map. -/
theorem matrixChartTensorEquiv_cancelBaseChange :
    (matrixChartTensorEquiv R B d c).toLinearMap.comp
        (cancelBaseChange R A B B ((Fin d → R) × (Fin c → R))).toLinearMap =
      (matrixChartTensorEquiv A B d c).toLinearMap.comp
        ((matrixChartTensorEquiv R A d c).toLinearMap.baseChange B) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro b x
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    rcases x with ⟨v, w⟩
    apply Prod.ext <;> ext i <;>
      simp [matrixChartTensorEquiv, Algebra.smul_def, mul_assoc,
        ← IsScalarTower.algebraMap_apply R A B]
  | add x y hx hy =>
    simp only [tmul_add, map_add]
    exact congrArg₂ (· + ·) hx hy

/-- Coordinate comparison after undoing the original coordinate identification. -/
theorem matrixChartTensorEquiv_cancelBaseChange_symm :
    ((matrixChartTensorEquiv R B d c).toLinearMap.comp
        (cancelBaseChange R A B B ((Fin d → R) × (Fin c → R))).toLinearMap).comp
        ((matrixChartTensorEquiv R A d c).symm.toLinearMap.baseChange B) =
      (matrixChartTensorEquiv A B d c).toLinearMap := by
  rw [matrixChartTensorEquiv_cancelBaseChange, LinearMap.comp_assoc,
    ← LinearMap.baseChange_comp]
  simp

/-- In normalized coordinates, the quotient-kernel base-change map
has the entrywise scalar-extended matrix. -/
theorem matrixFunctorPoint_baseChange_ker (C : Matrix (Fin d) (Fin c) A) :
    (LinearMap.ker (Module.Grassmannian.baseChangeMkQ B
      (matrixFunctorPoint R C).toSubmodule)).map
        (matrixChartTensorEquiv R B d c).toLinearMap =
      (matrixGrassmannianChartEquiv (C.map (algebraMap A B))).val.toSubmodule := by
  rw [grassmannian_baseChange_ker_eq_image, matrixFunctorPoint_submodule,
    baseChange_map]
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  rw [matrixChartTensorEquiv_cancelBaseChange_symm]
  exact matrixGrassmannianChart_submodule_baseChange B C

end Tower

variable {B : Type w} [CommRing B] [Algebra R B] (f : A →ₐ[R] B)

/-- The Grassmannian functor sends a normalized matrix point to its
entrywise image under the given algebra homomorphism. -/
theorem matrixFunctorPoint_map (C : Matrix (Fin d) (Fin c) A) :
    Module.Grassmannian.map f (matrixFunctorPoint R C) =
      matrixFunctorPoint R (C.map f) := by
  let : Algebra A B := f.toAlgebra
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' <|
    IsScalarTower.algebraMap_eq R A B
  apply Module.Grassmannian.ext
  apply (Submodule.orderIsoMapComap (matrixChartTensorEquiv R B d c)).injective
  change (Module.Grassmannian.map f (matrixFunctorPoint R C)).toSubmodule.map
      (matrixChartTensorEquiv R B d c).toLinearMap =
    (matrixFunctorPoint R (C.map f)).toSubmodule.map
      (matrixChartTensorEquiv R B d c).toLinearMap
  rw [Module.Grassmannian.map_toSubmodule, matrixFunctorPoint_baseChange_ker,
    matrixFunctorPoint_submodule, ← Submodule.map_comp]
  simp
  rfl

end FlagVarieties.Foundations.QuotientCharts
