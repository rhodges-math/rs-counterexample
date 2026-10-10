import RSCounterexample.FlagVarieties.Foundations.Flags.CoordinateGrassmannianComparison
import RSCounterexample.FlagVarieties.Foundations.Flags.MatrixChartFunctor

/-!
# Tower coherence for the coordinate Grassmannian quotient

Tensor-image scalar extension composes by the canonical tensor-tower map.
The finite-coordinate comparison commutes with that map, so the resulting
Grassmannian points are equal in the same ambient coordinate module.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

open TensorProduct AlgebraTensorModule

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- Iterated tensor images give the direct tensor image, without a flatness premise. -/
theorem submodule_baseChange_tower {M : Type*} [AddCommGroup M] [Module R M]
    (P : Submodule R M) :
    ((P.baseChange A).baseChange B).map (cancelBaseChange R A B B M).toLinearMap =
      P.baseChange B := by
  change ((LinearMap.range (P.subtype.baseChange A)).baseChange B).map _ = _
  have h : (cancelBaseChange R A B B M).toLinearMap.comp
      ((P.subtype.baseChange A).baseChange B) =
      (P.subtype.baseChange B).comp (cancelBaseChange R A B B P).toLinearMap := by
    rw [LinearMap.baseChange_baseChange]
    simp [← LinearMap.comp_assoc]
  rw [baseChange_range, ← LinearMap.range_comp, h, LinearMap.range_comp]
  rw [LinearMap.range_eq_top.mpr (cancelBaseChange R A B B P).surjective,
    Submodule.map_top]
  rfl

/-- The coordinate identification respects the tensor tower. -/
theorem coordinateTensorEquiv_cancelBaseChange (n : ℕ) :
    (TensorProduct.piScalarRight R B B (Fin n)).toLinearMap.comp
      (cancelBaseChange R A B B (Fin n → R)).toLinearMap =
    (TensorProduct.piScalarRight A B B (Fin n)).toLinearMap.comp
      ((TensorProduct.piScalarRight R A A (Fin n)).toLinearMap.baseChange B) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro b x
  induction x using TensorProduct.inductionOn with
  | tmul a v =>
    ext i
    simp [Algebra.smul_def, mul_assoc, ← IsScalarTower.algebraMap_apply R A B]
  | add x y hx hy =>
    simp only [tmul_add, map_add]
    exact congrArg₂ (· + ·) hx hy

/-- Scalar extension in ambient coordinates is transitive. -/
theorem coordinateGrassmannianBaseChange_tower {n d : ℕ}
    (P : Module.Grassmannian R (Fin n → R) d) :
    coordinateGrassmannianBaseChange B (coordinateGrassmannianBaseChange A P) =
      coordinateGrassmannianBaseChange B P := by
  apply Module.Grassmannian.ext
  rw [coordinateGrassmannianBaseChange_submodule,
    coordinateGrassmannianBaseChange_submodule,
    coordinateGrassmannianBaseChange_submodule, baseChange_map, ← Submodule.map_comp,
    ← coordinateTensorEquiv_cancelBaseChange, Submodule.map_comp, submodule_baseChange_tower]

end FlagVarieties.Foundations.QuotientCharts
