import Schubert.FlagVarieties.Foundations.Flags.SelectedChartNaturality
import Schubert.FlagVarieties.Foundations.Schemes.MatrixOverlapMap

/-!
# Universal regular maps for selected-coordinate overlaps

The universal matrix gives polynomial selected and remaining blocks for
each pair of coordinate selections. Their determinant localization is
exactly the applicability condition at every algebra-valued point, and
the regular inverse-block map evaluates to the quotient transition.
No representing Grassmannian scheme or global gluing is assumed here.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory

universe u

variable (R : Type u) [CommRing R] {n d : ℕ}

/-- The matrix with one independent polynomial variable in each entry. -/
def universalChartMatrix (d c : ℕ) : Matrix (Fin d) (Fin c) (MvPolynomial (Fin d × Fin c) R) :=
  fun i j => MvPolynomial.X (i, j)

/-- The selected block is computed from the universal quotient map. -/
def selectedPolynomialBlock (a b : Fin d ↪ Fin n) :
    Matrix (Fin d) (Fin d) (MvPolynomial (Fin d × Fin (n - d)) R) :=
  LinearMap.toMatrix' (selectedBlock (Matrix.toLin' (universalChartMatrix R d (n - d)))
    (selectedCoordinateChange a b))

/-- The remaining block of the same universal quotient. -/
def remainingPolynomialBlock (a b : Fin d ↪ Fin n) :
    Matrix (Fin d) (Fin (n - d)) (MvPolynomial (Fin d × Fin (n - d)) R) :=
  LinearMap.toMatrix' (remainingBlock (Matrix.toLin' (universalChartMatrix R d (n - d)))
    (selectedCoordinateChange a b))

variable {A : Type u} [CommRing A] [Algebra R A]

@[simp] theorem universalChartMatrix_evaluate {c : ℕ}
    (f : MvPolynomial (Fin d × Fin c) R →ₐ[R] A) :
    (universalChartMatrix R d c).map f = matrixEvaluationEquiv R d c A f := rfl

theorem selectedPolynomialBlock_evaluate (a b : Fin d ↪ Fin n)
    (f : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A) :
    (selectedPolynomialBlock R a b).map f =
      LinearMap.toMatrix' (selectedBlock (Matrix.toLin' (matrixEvaluationEquiv R d (n - d) A f))
        (selectedCoordinateChange a b)) := by
  exact selectedBlock_toMatrix_map f.toRingHom a b (universalChartMatrix R d (n - d))

theorem remainingPolynomialBlock_evaluate (a b : Fin d ↪ Fin n)
    (f : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A) :
    (remainingPolynomialBlock R a b).map f =
      LinearMap.toMatrix' (remainingBlock (Matrix.toLin' (matrixEvaluationEquiv R d (n - d) A f))
        (selectedCoordinateChange a b)) := by
  exact remainingBlock_toMatrix_map f.toRingHom a b (universalChartMatrix R d (n - d))

theorem selectedPolynomialBlock_det_evaluate (a b : Fin d ↪ Fin n)
    (f : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A) :
    f (selectedPolynomialBlock R a b).det =
      (LinearMap.toMatrix' (selectedBlock (Matrix.toLin' (matrixEvaluationEquiv R d (n - d) A f))
        (selectedCoordinateChange a b))).det := by
  rw [← selectedPolynomialBlock_evaluate R a b f]
  exact RingHom.map_det f.toRingHom _

/-- The polynomial determinant open is exactly the second selected-chart
condition for the original quotient represented by the evaluated matrix. -/
theorem selectedPolynomialBlock_open_iff
    (a b : Fin d ↪ Fin n) (f : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A)
    (P : Module.Grassmannian A (Fin n → A) d)
    (hP : (matrixGrassmannianChartEquiv (matrixEvaluationEquiv R d (n - d) A f)).val =
      grassmannianTransport P (selectedCoordinateEquiv a)) :
    IsUnit (f (selectedPolynomialBlock R a b).det) ↔
      Function.Bijective (P.toSubmodule.mkQ.comp (coordinateInclusion b)) := by
  rw [selectedPolynomialBlock_det_evaluate]
  exact (selectedMatrix_overlap_iff_isUnit_det P a b _ hP).symm

/-- A morphism from the universal determinant open to the second matrix chart. -/
def selectedChartOverlapMap (a b : Fin d ↪ Fin n) :
    Spec (CommRingCat.of (Localization.Away (selectedPolynomialBlock R a b).det)) ⟶
      Spec (CommRingCat.of (MvPolynomial (Fin d × Fin (n - d)) R)) :=
  matrixOverlapMap R (selectedPolynomialBlock R a b) (remainingPolynomialBlock R a b)

/-- The regular map evaluates to the normalized transition, not
merely to an unrelated rational expression with the same matrix sizes. -/
theorem selectedChartOverlapMap_evaluate (a b : Fin d ↪ Fin n)
    (f : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A)
    (h : IsUnit (f (selectedPolynomialBlock R a b).det))
    (hbij : Function.Bijective (selectedBlock
      (Matrix.toLin' (matrixEvaluationEquiv R d (n - d) A f)) (selectedCoordinateChange a b))) :
    matrixEvaluationEquiv R d (n - d) A
      ((IsLocalization.Away.liftAlgHom (selectedPolynomialBlock R a b).det h :
        Localization.Away (selectedPolynomialBlock R a b).det →ₐ[R] A).comp
          (matrixOverlapCoordinates R (selectedPolynomialBlock R a b)
            (remainingPolynomialBlock R a b))) =
      LinearMap.toMatrix' (transition
        (Matrix.toLin' (matrixEvaluationEquiv R d (n - d) A f))
        (selectedCoordinateChange a b) hbij) := by
  rw [matrixOverlapCoordinates_evaluate, selectedPolynomialBlock_evaluate,
    remainingPolynomialBlock_evaluate, toMatrix_transition]

/-- At every point of the determinant open, the regular map presents the
same quotient in the second selected coordinates. -/
theorem selectedChartOverlapMap_represents_quotient
    (a b : Fin d ↪ Fin n) (f : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A)
    (h : IsUnit (f (selectedPolynomialBlock R a b).det))
    (P : Module.Grassmannian A (Fin n → A) d)
    (hP : (matrixGrassmannianChartEquiv (matrixEvaluationEquiv R d (n - d) A f)).val =
      grassmannianTransport P (selectedCoordinateEquiv a)) :
    (matrixGrassmannianChartEquiv
      (matrixEvaluationEquiv R d (n - d) A
        ((IsLocalization.Away.liftAlgHom (selectedPolynomialBlock R a b).det h :
          Localization.Away (selectedPolynomialBlock R a b).det →ₐ[R] A).comp
            (matrixOverlapCoordinates R (selectedPolynomialBlock R a b)
              (remainingPolynomialBlock R a b))))).val =
      grassmannianTransport P (selectedCoordinateEquiv b) := by
  have hdet := h
  rw [selectedPolynomialBlock_det_evaluate] at hdet
  have hbij := (chartCondition_transport_iff _ _).mp
    ((chartCondition_transport_iff_isUnit_det _ _).mpr hdet)
  rw [selectedChartOverlapMap_evaluate R a b f h hbij]
  exact selectedMatrix_transition_eq P a b _ hP hbij

end FlagVarieties.Foundations.QuotientCharts
