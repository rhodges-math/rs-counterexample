import RSCounterexample.FlagVarieties.Foundations.Flags.QuotientChart
import RSCounterexample.FlagVarieties.Foundations.Flags.BaseChangeImages
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Base change of normalized quotient charts

The kernel of `[id C]` is the graph of `-C`. Tensoring its image
and transporting by the canonical product equivalence gives the kernel
of `[id (C.baseChange B)]`. No flatness or projectivity assumption is needed.
These are module identities; chart coverage is `Flags/CoordinateChartCover.lean`.
-/

namespace FlagVarieties.Foundations.QuotientCharts

open TensorProduct

variable {R U V : Type*} [CommRing R]
  [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]

/-- The graph parametrization of the normalized kernel. -/
def kernelGraph (C : V →ₗ[R] U) : V →ₗ[R] (U × V) :=
  (-C).prod LinearMap.id

@[simp] theorem kernelGraph_apply (C : V →ₗ[R] U) (v : V) :
    kernelGraph C v = (-C v, v) := rfl

theorem normalizedMap_ker_eq_range (C : V →ₗ[R] U) :
    LinearMap.ker (normalizedMap C) = LinearMap.range (kernelGraph C) := by
  ext x
  rw [mem_normalizedMap_ker, LinearMap.mem_range]
  constructor
  · intro h
    exact ⟨x.2, Prod.ext h.symm rfl⟩
  · rintro ⟨v, hv⟩
    rw [← hv]
    rfl

variable (B : Type*) [CommRing B] [Algebra R B]

/-- The normalized quotient map commutes with scalar extension. -/
theorem normalizedMap_baseChange (C : V →ₗ[R] U) :
    (normalizedMap C).baseChange B =
      (normalizedMap (C.baseChange B)).comp
        (TensorProduct.prodRight R B B U V).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro b x
  simp [normalizedMap_apply, tmul_add]

/-- The graph inclusion commutes with scalar extension. -/
theorem kernelGraph_baseChange (C : V →ₗ[R] U) :
    (TensorProduct.prodRight R B B U V).toLinearMap.comp ((kernelGraph C).baseChange B) =
      kernelGraph (C.baseChange B) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro b v
  simp [kernelGraph_apply, tmul_neg]

/-- Tensor images of normalized kernels have exactly the expected normalized
presentation after the canonical product identification. -/
theorem normalizedMap_ker_baseChange (C : V →ₗ[R] U) :
    ((LinearMap.ker (normalizedMap C)).baseChange B).map
        (TensorProduct.prodRight R B B U V).toLinearMap =
      LinearMap.ker (normalizedMap (C.baseChange B)) := by
  rw [normalizedMap_ker_eq_range, baseChange_range, ← LinearMap.range_comp,
    kernelGraph_baseChange, ← normalizedMap_ker_eq_range]

/-- Every chart kernel stays in the normalized chart after any base
change, with the scalar extension of its uniquely determined coefficients. -/
theorem chart_kernel_baseChange (P : Submodule R (U × V)) (h : ChartCondition P) :
    (P.baseChange B).map (TensorProduct.prodRight R B B U V).toLinearMap =
      LinearMap.ker (normalizedMap ((coefficients P h).baseChange B)) := by
  conv_lhs => rw [← normalizedMap_coefficients_ker P h]
  exact normalizedMap_ker_baseChange B _

theorem chartCondition_baseChange (P : Submodule R (U × V)) (h : ChartCondition P) :
    ChartCondition ((P.baseChange B).map (TensorProduct.prodRight R B B U V).toLinearMap) := by
  rw [chart_kernel_baseChange B P h]
  exact normalizedMap_chartCondition _

theorem coefficients_baseChange (P : Submodule R (U × V)) (h : ChartCondition P) :
    coefficients ((P.baseChange B).map (TensorProduct.prodRight R B B U V).toLinearMap)
      (chartCondition_baseChange B P h) = (coefficients P h).baseChange B := by
  apply normalizedMap_ker_injective
  change LinearMap.ker (normalizedMap (coefficients _ _)) =
    LinearMap.ker (normalizedMap ((coefficients P h).baseChange B))
  rw [normalizedMap_coefficients_ker, chart_kernel_baseChange]

end FlagVarieties.Foundations.QuotientCharts
