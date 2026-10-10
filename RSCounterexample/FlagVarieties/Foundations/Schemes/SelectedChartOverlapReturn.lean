import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedChartOverlapMap

/-!
# Return maps on selected-coordinate overlaps

Every algebra-valued matrix defines a quotient in its selected
ambient coordinates. The regular transition presents that quotient in
the new coordinates. Consequently its reverse determinant is a unit and
the reverse transition recovers the original polynomial evaluation map.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

universe u

variable (R : Type u) [CommRing R] {n d : ℕ}
  {A : Type u} [CommRing A] [Algebra R A]

/-- The quotient represented by an algebra-valued selected chart. -/
def selectedChartPoint (a : Fin d ↪ Fin n)
    (f : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A) :
    Module.Grassmannian A (Fin n → A) d :=
  grassmannianTransport (matrixGrassmannianChartEquiv (matrixEvaluationEquiv R d (n - d) A f)).val
    (selectedCoordinateEquiv a).symm

theorem selectedChartPoint_presented (a : Fin d ↪ Fin n)
    (f : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A) :
    (matrixGrassmannianChartEquiv (matrixEvaluationEquiv R d (n - d) A f)).val =
      grassmannianTransport (selectedChartPoint R a f) (selectedCoordinateEquiv a) := by
  unfold selectedChartPoint
  exact (grassmannianTransport_symm
    (matrixGrassmannianChartEquiv (matrixEvaluationEquiv R d (n - d) A f)).val
    (selectedCoordinateEquiv (R := A) a).symm).symm

/-- Evaluate the regular overlap map at a point of its determinant open. -/
def selectedChartTransitionHom (a b : Fin d ↪ Fin n)
    (f : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A)
    (h : IsUnit (f (selectedPolynomialBlock R a b).det)) :
    MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A :=
  (IsLocalization.Away.liftAlgHom (selectedPolynomialBlock R a b).det h :
    Localization.Away (selectedPolynomialBlock R a b).det →ₐ[R] A).comp
      (matrixOverlapCoordinates R (selectedPolynomialBlock R a b) (remainingPolynomialBlock R a b))

theorem selectedChartTransitionHom_represents (a b : Fin d ↪ Fin n)
    (f : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A)
    (h : IsUnit (f (selectedPolynomialBlock R a b).det))
    (P : Module.Grassmannian A (Fin n → A) d)
    (hP : (matrixGrassmannianChartEquiv (matrixEvaluationEquiv R d (n - d) A f)).val =
      grassmannianTransport P (selectedCoordinateEquiv a)) :
    (matrixGrassmannianChartEquiv
      (matrixEvaluationEquiv R d (n - d) A (selectedChartTransitionHom R a b f h))).val =
      grassmannianTransport P (selectedCoordinateEquiv b) :=
  selectedChartOverlapMap_represents_quotient R a b f h P hP

/-- Applicability of the starting chart is intrinsic to the represented quotient. -/
theorem selectedChartPoint_selected_bijective (a : Fin d ↪ Fin n)
    (f : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A) :
    Function.Bijective
      ((selectedChartPoint R a f).toSubmodule.mkQ.comp (coordinateInclusion a)) := by
  apply (selectedCoordinate_chartCondition_iff _ a).mp
  change ChartCondition (grassmannianTransport (selectedChartPoint R a f)
    (selectedCoordinateEquiv a)).toSubmodule
  rw [← selectedChartPoint_presented]
  exact (matrixGrassmannianChartEquiv (matrixEvaluationEquiv R d (n - d) A f)).property

/-- The regular transition always lands in the reverse determinant open. -/
theorem selectedChartTransitionHom_reverse_unit (a b : Fin d ↪ Fin n)
    (f : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A)
    (h : IsUnit (f (selectedPolynomialBlock R a b).det)) :
    IsUnit (selectedChartTransitionHom R a b f h (selectedPolynomialBlock R b a).det) := by
  apply (selectedPolynomialBlock_open_iff R b a _ (selectedChartPoint R a f)
    (selectedChartTransitionHom_represents R a b f h _ (selectedChartPoint_presented R a f))).mpr
  exact selectedChartPoint_selected_bijective R a f

/-- Returning through the regular reverse overlap recovers the original
algebra-valued point as an equality of polynomial algebra maps. -/
theorem selectedChartTransitionHom_roundtrip (a b : Fin d ↪ Fin n)
    (f : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A)
    (h : IsUnit (f (selectedPolynomialBlock R a b).det))
    (hback : IsUnit (selectedChartTransitionHom R a b f h (selectedPolynomialBlock R b a).det)) :
    selectedChartTransitionHom R b a (selectedChartTransitionHom R a b f h) hback = f := by
  apply (matrixEvaluationEquiv R d (n - d) A).injective
  apply matrixGrassmannianChartEquiv.injective
  apply Subtype.ext
  exact (selectedChartTransitionHom_represents R b a _ hback (selectedChartPoint R a f)
    (selectedChartTransitionHom_represents R a b f h _ (selectedChartPoint_presented R a f))).trans
      (selectedChartPoint_presented R a f).symm

end FlagVarieties.Foundations.QuotientCharts
