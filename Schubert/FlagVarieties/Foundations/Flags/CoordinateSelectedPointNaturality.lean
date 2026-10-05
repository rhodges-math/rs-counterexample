import Schubert.FlagVarieties.Foundations.Flags.CoordinateBaseChangeCoherence
import Schubert.FlagVarieties.Foundations.Schemes.SelectedChartOverlapReturn

/-!
# Scalar naturality of selected-coordinate quotient points

The selected coordinate ordering commutes with the canonical tensor
comparison. Together with normalized matrix base change, this identifies
the quotient kernel after arbitrary scalar extension.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

open TensorProduct

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {n d : ℕ}

/-- Selected and complementary coordinate ordering commutes with scalar extension. -/
theorem selectedCoordinateEquiv_baseChange (a : Fin d ↪ Fin n) :
    (matrixChartTensorEquiv A B d (n - d)).toLinearMap.comp
      ((selectedCoordinateEquiv (R := A) a).toLinearMap.baseChange B) =
    (selectedCoordinateEquiv (R := B) a).toLinearMap.comp
      (TensorProduct.piScalarRight A B B (Fin n)).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro b v
  apply Prod.ext <;> ext i <;> simp [matrixChartTensorEquiv]

/-- Undoing a selected ordering commutes with the same coordinate comparison. -/
theorem selectedCoordinateEquiv_symm_baseChange (a : Fin d ↪ Fin n) :
    (TensorProduct.piScalarRight A B B (Fin n)).toLinearMap.comp
      ((selectedCoordinateEquiv (R := A) a).symm.toLinearMap.baseChange B) =
    (selectedCoordinateEquiv (R := B) a).symm.toLinearMap.comp
      (matrixChartTensorEquiv A B d (n - d)).toLinearMap := by
  have h := selectedCoordinateEquiv_baseChange (A := A) (B := B) a
  have hc := congrArg (fun t => t.comp
    ((selectedCoordinateEquiv (R := A) a).symm.toLinearMap.baseChange B)) h
  rw [LinearMap.comp_assoc, ← LinearMap.baseChange_comp] at hc
  simp at hc
  apply LinearMap.ext
  intro v
  apply (selectedCoordinateEquiv (R := B) a).injective
  simpa using (LinearMap.congr_fun hc v).symm

/-- Coordinate scalar extension of a normalized selected quotient has the extended matrix. -/
theorem selectedMatrixPoint_baseChange (a : Fin d ↪ Fin n)
    (C : Matrix (Fin d) (Fin (n - d)) A) :
    coordinateGrassmannianBaseChange B
      (grassmannianTransport (matrixGrassmannianChartEquiv C).val
        (selectedCoordinateEquiv (R := A) a).symm) =
      grassmannianTransport (matrixGrassmannianChartEquiv (C.map (algebraMap A B))).val
        (selectedCoordinateEquiv (R := B) a).symm := by
  apply Module.Grassmannian.ext
  rw [coordinateGrassmannianBaseChange_submodule, grassmannianTransport_submodule,
    grassmannianTransport_submodule, baseChange_map, ← Submodule.map_comp,
    selectedCoordinateEquiv_symm_baseChange, Submodule.map_comp,
    matrixGrassmannianChart_submodule_baseChange]

universe u

variable (R : Type u) [CommRing R] {A B : Type u} [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (g : A →ₐ[R] B)

/-- The given algebra map extends the selected quotient in the same ambient coordinates. -/
theorem selectedChartPoint_baseChange (a : Fin d ↪ Fin n)
    (f : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A) :
    letI : Algebra A B := g.toAlgebra
    coordinateGrassmannianBaseChange B (selectedChartPoint R a f) =
      selectedChartPoint R a (g.comp f) := by
  let : Algebra A B := g.toAlgebra
  unfold selectedChartPoint
  rw [selectedMatrixPoint_baseChange, matrixEvaluationEquiv_comp]
  rfl

/-- Naturality for the existing scalar-tower algebra structures. -/
theorem selectedChartPoint_baseChange_tower [Algebra A B] [IsScalarTower R A B]
    (a : Fin d ↪ Fin n)
    (f : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A) :
    coordinateGrassmannianBaseChange B (selectedChartPoint R a f) =
      selectedChartPoint R a ((IsScalarTower.toAlgHom R A B).comp f) := by
  unfold selectedChartPoint
  rw [selectedMatrixPoint_baseChange, matrixEvaluationEquiv_comp]
  rfl

end FlagVarieties.Foundations.QuotientCharts
