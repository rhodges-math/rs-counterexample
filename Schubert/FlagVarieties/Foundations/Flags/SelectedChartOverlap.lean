import Schubert.FlagVarieties.Foundations.Flags.SelectedCoordinateChart
import Schubert.FlagVarieties.Foundations.Flags.QuotientChartTransition

/-!
# Selected-coordinate chart overlaps

For two selections in the same ambient coordinate module, applicability of
the second chart is the unit-determinant condition on its selected quotient
block. The normalized transition presents the same original quotient.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

variable {R : Type*} [CommRing R] {n d : ℕ}

/-- Change between two selected-coordinate orders of the same ambient module. -/
def selectedCoordinateChange (a b : Fin d ↪ Fin n) :
    ((Fin d → R) × (Fin (n - d) → R)) ≃ₗ[R]
      ((Fin d → R) × (Fin (n - d) → R)) :=
  (selectedCoordinateEquiv a).symm.trans (selectedCoordinateEquiv b)

theorem selectedCoordinateChange_transport
    (P : Module.Grassmannian R (Fin n → R) d) (a b : Fin d ↪ Fin n) :
    grassmannianTransport (grassmannianTransport P (selectedCoordinateEquiv a))
      (selectedCoordinateChange a b) = grassmannianTransport P (selectedCoordinateEquiv b) := by
  rw [grassmannianTransport_trans]
  congr 1
  apply LinearEquiv.ext
  intro v
  change selectedCoordinateEquiv b
    ((selectedCoordinateEquiv a).symm (selectedCoordinateEquiv a v)) = selectedCoordinateEquiv b v
  rw [LinearEquiv.symm_apply_apply]

/-- If one matrix presents the quotient, the other selected coordinates
apply exactly on its invertible selected-determinant locus. -/
theorem selectedMatrix_overlap_iff_isUnit_det
    (P : Module.Grassmannian R (Fin n → R) d) (a b : Fin d ↪ Fin n)
    (C : Matrix (Fin d) (Fin (n - d)) R)
    (hC : (matrixGrassmannianChartEquiv C).val =
      grassmannianTransport P (selectedCoordinateEquiv a)) :
    Function.Bijective (P.toSubmodule.mkQ.comp (coordinateInclusion b)) ↔
      IsUnit (LinearMap.toMatrix'
        (selectedBlock (Matrix.toLin' C) (selectedCoordinateChange a b))).det := by
  have he : grassmannianTransport (matrixGrassmannianChartEquiv C).val
      (selectedCoordinateChange a b) = grassmannianTransport P (selectedCoordinateEquiv b) := by
    rw [hC, selectedCoordinateChange_transport]
  rw [← selectedCoordinate_chartCondition_iff P.toSubmodule b]
  change ChartCondition (grassmannianTransport P (selectedCoordinateEquiv b)).toSubmodule ↔ _
  rw [← he]
  exact chartCondition_transport_iff_isUnit_det C (selectedCoordinateChange a b)

/-- The normalized inverse-block transition represents the original quotient
in the second selected-coordinate chart. -/
theorem selectedMatrix_transition_eq
    (P : Module.Grassmannian R (Fin n → R) d) (a b : Fin d ↪ Fin n)
    (C : Matrix (Fin d) (Fin (n - d)) R)
    (hC : (matrixGrassmannianChartEquiv C).val =
      grassmannianTransport P (selectedCoordinateEquiv a))
    (h : Function.Bijective (selectedBlock (Matrix.toLin' C) (selectedCoordinateChange a b))) :
    (matrixGrassmannianChartEquiv
      (LinearMap.toMatrix' (transition (Matrix.toLin' C) (selectedCoordinateChange a b) h))).val =
        grassmannianTransport P (selectedCoordinateEquiv b) := by
  have he : grassmannianTransport (matrixGrassmannianChartEquiv C).val
      (selectedCoordinateChange a b) = grassmannianTransport P (selectedCoordinateEquiv b) := by
    rw [hC, selectedCoordinateChange_transport]
  rw [← he]
  apply Module.Grassmannian.ext
  simp only [matrixGrassmannianChartEquiv_submodule, Matrix.toLin'_toMatrix',
    grassmannianTransport_submodule]
  exact normalizedMap_transition_ker _ _ h

end FlagVarieties.Foundations.QuotientCharts
