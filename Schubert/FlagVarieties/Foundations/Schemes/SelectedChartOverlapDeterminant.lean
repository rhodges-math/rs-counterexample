import Schubert.FlagVarieties.Foundations.Flags.SelectedChartInverseBlock
import Schubert.FlagVarieties.Foundations.Schemes.SelectedChartOverlapIso

/-! # Reciprocal determinants on the selected-chart intersection

The reverse chart's selected determinant is the reciprocal of the forward
determinant. In particular the two chart coordinate rings generate the
localization, a prerequisite for the separatedness proof.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts

universe u

variable (R : Type u) [CommRing R] {n d : ℕ} (a b : Fin d ↪ Fin n)

theorem selectedChartTransitionHom_det_mul
    {A : Type u} [CommRing A] [Algebra R A]
    (f : MvPolynomial (Fin d × Fin (n-d)) R →ₐ[R] A)
    (h : IsUnit (f (selectedPolynomialBlock R a b).det)) :
    f (selectedPolynomialBlock R a b).det *
        selectedChartTransitionHom R a b f h (selectedPolynomialBlock R b a).det = 1 := by
  have hdet := h
  rw [selectedPolynomialBlock_det_evaluate] at hdet
  have hbij := (chartCondition_transport_iff _ _).mp
    ((chartCondition_transport_iff_isUnit_det _ _).mpr hdet)
  have ht := selectedChartOverlapMap_evaluate R a b f h hbij
  rw [selectedPolynomialBlock_det_evaluate R b a,
    show matrixEvaluationEquiv R d (n-d) A (selectedChartTransitionHom R a b f h) =
      LinearMap.toMatrix' (transition (Matrix.toLin' (matrixEvaluationEquiv R d (n-d) A f))
        (selectedCoordinateChange a b) hbij) from ht,
    Matrix.toLin'_toMatrix', selectedBlock_transition_matrix,
    selectedPolynomialBlock_det_evaluate, ← Matrix.det_mul,
    Matrix.mul_nonsing_inv _ hdet, Matrix.det_one]

/-- The regular reverse determinant is the forward localization inverse. -/
theorem selectedOverlapCoordinates_det_mul :
    algebraMap _ (Localization.Away (selectedPolynomialBlock R a b).det)
        (selectedPolynomialBlock R a b).det *
      matrixOverlapCoordinates R (selectedPolynomialBlock R a b)
        (remainingPolynomialBlock R a b) (selectedPolynomialBlock R b a).det = 1 := by
  have h := selectedChartTransitionHom_det_mul R a b
    (IsScalarTower.toAlgHom R (MvPolynomial (Fin d × Fin (n-d)) R)
      (Localization.Away (selectedPolynomialBlock R a b).det))
    (IsLocalization.Away.algebraMap_isUnit (selectedPolynomialBlock R a b).det)
  rw [selectedChartTransitionHom_algebraMap R a b
    (IsLocalization.Away.algebraMap_isUnit (selectedPolynomialBlock R a b).det)] at h
  exact h

end FlagVarieties.Foundations.QuotientCharts
