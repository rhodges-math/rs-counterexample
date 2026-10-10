import RSCounterexample.FlagVarieties.Foundations.Flags.GrassmannianChart
import RSCounterexample.FlagVarieties.Foundations.Flags.QuotientChartBaseChange
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Entrywise scalar extension in the normalized matrix chart

The canonical finite-coordinate identifications send the scalar extension
of a matrix map to its entrywise algebra-map image. Consequently the
normalized Grassmannian submodule has the expected matrix after base change.
No scheme representability or open-cover result is used.
-/

namespace FlagVarieties.Foundations.QuotientCharts

open TensorProduct
open scoped BigOperators

variable {R : Type*} [CommRing R] (B : Type*) [CommRing B] [Algebra R B]
  {d c : ℕ}

/-- Scalar extension of a matrix map is entrywise scalar extension. -/
theorem matrix_toLin_baseChange (C : Matrix (Fin d) (Fin c) R) :
    (TensorProduct.piScalarRight R B B (Fin d)).toLinearMap.comp
        ((Matrix.toLin' C).baseChange B) =
      (Matrix.toLin' (C.map (algebraMap R B))).comp
        (TensorProduct.piScalarRight R B B (Fin c)).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro b v
  ext i
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Algebra.smul_def,
    Finset.sum_mul, mul_assoc]

/-- The canonical identification of scalar-extended selected and remaining
coordinate spaces with their coordinates over the new ring. -/
noncomputable def matrixChartTensorEquiv (R : Type*) [CommRing R]
    (B : Type*) [CommRing B] [Algebra R B] (d c : ℕ) :
    B ⊗[R] ((Fin d → R) × (Fin c → R)) ≃ₗ[B] ((Fin d → B) × (Fin c → B)) :=
  (TensorProduct.prodRight R B B _ _).trans
    ((TensorProduct.piScalarRight R B B (Fin d)).prodCongr
      (TensorProduct.piScalarRight R B B (Fin c)))

/-- The graph of the normalized matrix has entrywise scalar extension. -/
theorem matrix_kernelGraph_baseChange (C : Matrix (Fin d) (Fin c) R) :
    (matrixChartTensorEquiv R B d c).toLinearMap.comp
        ((kernelGraph (Matrix.toLin' C)).baseChange B) =
      (kernelGraph (Matrix.toLin' (C.map (algebraMap R B)))).comp
        (TensorProduct.piScalarRight R B B (Fin c)).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro b v
  apply Prod.ext
  · ext i
    have h := congrFun (LinearMap.congr_fun (matrix_toLin_baseChange B C) (b ⊗ₜ[R] v)) i
    simpa [matrixChartTensorEquiv, kernelGraph_apply] using congrArg Neg.neg h
  · simp [matrixChartTensorEquiv, kernelGraph_apply]

/-- The Grassmannian submodule from the matrix chart transforms to
the submodule of the entrywise scalar-extended matrix, without flatness. -/
theorem matrixGrassmannianChart_submodule_baseChange (C : Matrix (Fin d) (Fin c) R) :
    (((matrixGrassmannianChartEquiv C).val.toSubmodule).baseChange B).map
        (matrixChartTensorEquiv R B d c).toLinearMap =
      (matrixGrassmannianChartEquiv (C.map (algebraMap R B))).val.toSubmodule := by
  simp only [matrixGrassmannianChartEquiv_submodule, normalizedMap_ker_eq_range]
  rw [baseChange_range, ← LinearMap.range_comp, matrix_kernelGraph_baseChange,
    LinearMap.range_comp]
  rw [LinearMap.range_eq_top.mpr (TensorProduct.piScalarRight R B B (Fin c)).surjective,
    Submodule.map_top]

end FlagVarieties.Foundations.QuotientCharts
