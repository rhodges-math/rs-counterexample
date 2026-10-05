import Schubert.FlagVarieties.Foundations.Flags.GrassmannianChart
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Coordinate transitions between normalized quotient charts

After changing ambient coordinates, the selected quotient block must be
invertible. Its inverse normalizes the remaining block. For finite coordinate
spaces the applicability condition is exactly that the selected determinant
is a unit. The corresponding open subschemes and regular transition maps
are in `Schemes/MatrixOverlapMap.lean` and `Schemes/SelectedChartGlueData.lean`.
-/

namespace FlagVarieties.Foundations.QuotientCharts

variable {R U V : Type*} [CommRing R]
  [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]

/-- The selected block of the quotient map in the new ambient coordinates. -/
def selectedBlock (C : V →ₗ[R] U) (e : (U × V) ≃ₗ[R] (U × V)) : U →ₗ[R] U :=
  ((normalizedMap C).comp e.symm.toLinearMap).comp (LinearMap.inl R U V)

/-- The remaining block of the same quotient map. -/
def remainingBlock (C : V →ₗ[R] U) (e : (U × V) ≃ₗ[R] (U × V)) : V →ₗ[R] U :=
  ((normalizedMap C).comp e.symm.toLinearMap).comp (LinearMap.inr R U V)

/-- The transported quotient is still identified with the old target. -/
noncomputable def transportedQuotientFrame (C : V →ₗ[R] U)
    (e : (U × V) ≃ₗ[R] (U × V)) :
    ((U × V) ⧸ (LinearMap.ker (normalizedMap C)).map e.toLinearMap) ≃ₗ[R] U :=
  (Submodule.Quotient.equiv (LinearMap.ker (normalizedMap C)) _ e rfl).symm.trans
    (normalizedQuotientEquiv C)

@[simp] theorem transportedQuotientFrame_mk (C : V →ₗ[R] U)
    (e : (U × V) ≃ₗ[R] (U × V)) (x : U × V) :
    transportedQuotientFrame C e (Submodule.Quotient.mk x) =
      normalizedMap C (e.symm x) := by
  simp [transportedQuotientFrame]

theorem transportedQuotientFrame_firstCoordinates (C : V →ₗ[R] U)
    (e : (U × V) ≃ₗ[R] (U × V)) :
    (transportedQuotientFrame C e).toLinearMap.comp
        (firstCoordinates ((LinearMap.ker (normalizedMap C)).map e.toLinearMap)) =
      selectedBlock C e := by
  ext u
  simp [firstCoordinates_apply, selectedBlock]

/-- Applicability of the second chart is invertibility of its selected block. -/
theorem chartCondition_transport_iff (C : V →ₗ[R] U)
    (e : (U × V) ≃ₗ[R] (U × V)) :
    ChartCondition ((LinearMap.ker (normalizedMap C)).map e.toLinearMap) ↔
      Function.Bijective (selectedBlock C e) := by
  rw [← transportedQuotientFrame_firstCoordinates]
  exact ((transportedQuotientFrame C e).bijective.of_comp_iff' _).symm

/-- Normalize the remaining block by the inverse selected block. -/
noncomputable def transition (C : V →ₗ[R] U) (e : (U × V) ≃ₗ[R] (U × V))
    (h : Function.Bijective (selectedBlock C e)) : V →ₗ[R] U :=
  (LinearEquiv.ofBijective (selectedBlock C e) h).symm.toLinearMap.comp (remainingBlock C e)

theorem normalizedMap_transition (C : V →ₗ[R] U)
    (e : (U × V) ≃ₗ[R] (U × V)) (h : Function.Bijective (selectedBlock C e)) :
    normalizedMap (transition C e h) =
      (LinearEquiv.ofBijective (selectedBlock C e) h).symm.toLinearMap.comp
        ((normalizedMap C).comp e.symm.toLinearMap) := by
  apply LinearMap.ext
  rintro ⟨u, v⟩
  change u + (LinearEquiv.ofBijective (selectedBlock C e) h).symm (remainingBlock C e v) =
    (LinearEquiv.ofBijective (selectedBlock C e) h).symm (normalizedMap C (e.symm (u, v)))
  have hx : (u, v) = (u, (0 : V)) + ((0 : U), v) := by simp
  rw [hx, map_add, map_add, map_add]
  congr 1
  exact ((LinearEquiv.ofBijective (selectedBlock C e) h).symm_apply_apply u).symm

/-- The transition presents exactly the transported submodule. -/
theorem normalizedMap_transition_ker (C : V →ₗ[R] U)
    (e : (U × V) ≃ₗ[R] (U × V)) (h : Function.Bijective (selectedBlock C e)) :
    LinearMap.ker (normalizedMap (transition C e h)) =
      (LinearMap.ker (normalizedMap C)).map e.toLinearMap := by
  rw [normalizedMap_transition, LinearEquiv.ker_comp, LinearMap.ker_comp]
  exact ((LinearMap.ker (normalizedMap C)).map_equiv_eq_comap_symm e).symm

/-- The transition formula agrees with the previously defined unique chart coefficients. -/
theorem coefficients_transport (C : V →ₗ[R] U)
    (e : (U × V) ≃ₗ[R] (U × V)) (h : Function.Bijective (selectedBlock C e)) :
    coefficients ((LinearMap.ker (normalizedMap C)).map e.toLinearMap)
      ((chartCondition_transport_iff C e).mpr h) = transition C e h := by
  apply normalizedMap_ker_injective
  change LinearMap.ker (normalizedMap (coefficients _ _)) =
    LinearMap.ker (normalizedMap (transition C e h))
  rw [normalizedMap_coefficients_ker, normalizedMap_transition_ker]

/-- For finite coordinates the chart overlap is the invertible-determinant locus. -/
theorem chartCondition_transport_iff_isUnit_det {d c : ℕ}
    (C : Matrix (Fin d) (Fin c) R)
    (e : ((Fin d → R) × (Fin c → R)) ≃ₗ[R] ((Fin d → R) × (Fin c → R))) :
    ChartCondition ((LinearMap.ker (normalizedMap (Matrix.toLin' C))).map e.toLinearMap) ↔
      IsUnit (LinearMap.toMatrix' (selectedBlock (Matrix.toLin' C) e)).det := by
  rw [chartCondition_transport_iff, ← Module.End.isUnit_iff,
    ← LinearMap.isUnit_toMatrix'_iff, Matrix.isUnit_iff_isUnit_det]

end FlagVarieties.Foundations.QuotientCharts
