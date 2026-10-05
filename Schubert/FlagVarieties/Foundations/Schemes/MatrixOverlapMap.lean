import Schubert.FlagVarieties.Foundations.Flags.MatrixChartTransitionFormula
import Schubert.FlagVarieties.Foundations.Flags.MatrixChartParameters
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Regular inverse-block maps on a determinant open

For matrices `L,N` over any base algebra, the expression `L⁻¹ N` defines
a scheme morphism from the localization at `det L` to matrix
affine space. Evaluation at every algebra-valued point is the same
inverse-block formula. Taking the base algebra to be a polynomial ring
gives the regular maps needed for chart overlaps; they are used for the
chart gluing in `Schemes/SelectedChartGlueData.lean`.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory

universe u

variable (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
  {d c : ℕ} (L : Matrix (Fin d) (Fin d) A) (N : Matrix (Fin d) (Fin c) A)

/-- Coordinates after inverting the selected determinant. -/
def localizedTransitionEntries : Matrix (Fin d) (Fin c) (Localization.Away L.det) :=
  (L.map (algebraMap A (Localization.Away L.det)))⁻¹ *
    N.map (algebraMap A (Localization.Away L.det))

theorem localized_selected_det_isUnit :
    IsUnit (L.map (algebraMap A (Localization.Away L.det))).det := by
  change IsUnit ((algebraMap A (Localization.Away L.det)).mapMatrix L).det
  rw [← RingHom.map_det]
  exact IsLocalization.Away.algebraMap_isUnit L.det

/-- The coordinate-ring homomorphism defining the regular inverse-block map. -/
def matrixOverlapCoordinates :
    MvPolynomial (Fin d × Fin c) R →ₐ[R] Localization.Away L.det :=
  MvPolynomial.aeval (fun ij => localizedTransitionEntries L N ij.1 ij.2)

/-- A scheme morphism on the determinant localization. -/
def matrixOverlapMap :
    Spec (CommRingCat.of (Localization.Away L.det)) ⟶
      Spec (CommRingCat.of (MvPolynomial (Fin d × Fin c) R)) :=
  Spec.map (CommRingCat.ofHom (matrixOverlapCoordinates R L N).toRingHom)

@[simp] theorem matrixOverlapCoordinates_X (i : Fin d) (j : Fin c) :
    matrixOverlapCoordinates R L N (MvPolynomial.X (i, j)) =
      localizedTransitionEntries L N i j := by
  simp [matrixOverlapCoordinates]

theorem localizedTransitionEntries_evaluate {B : Type u} [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (h : IsUnit (f L.det)) :
    (localizedTransitionEntries L N).map
        (IsLocalization.Away.liftAlgHom L.det h : Localization.Away L.det →ₐ[R] B) =
      (L.map f)⁻¹ * N.map f := by
  unfold localizedTransitionEntries
  let g : Localization.Away L.det →ₐ[R] B := IsLocalization.Away.liftAlgHom L.det h
  change ((L.map (algebraMap A (Localization.Away L.det)))⁻¹ *
    N.map (algebraMap A (Localization.Away L.det))).map g.toRingHom = _
  rw [map_matrix_transition_of_isUnit_det g.toRingHom _ _ (localized_selected_det_isUnit L)]
  have hL : (L.map (algebraMap A (Localization.Away L.det))).map g.toRingHom = L.map f := by
    ext i j
    simp [g, Matrix.map, IsLocalization.Away.liftAlgHom_apply]
  have hN : (N.map (algebraMap A (Localization.Away L.det))).map g.toRingHom = N.map f := by
    ext i j
    simp [g, Matrix.map, IsLocalization.Away.liftAlgHom_apply]
  rw [hL, hN]

/-- Every algebra-valued point of the determinant open evaluates to `L⁻¹ N`. -/
theorem matrixOverlapCoordinates_evaluate {B : Type u} [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (h : IsUnit (f L.det)) :
    matrixEvaluationEquiv R d c B
      ((IsLocalization.Away.liftAlgHom L.det h : Localization.Away L.det →ₐ[R] B).comp
        (matrixOverlapCoordinates R L N)) = (L.map f)⁻¹ * N.map f := by
  rw [matrixEvaluationEquiv_comp]
  have he : matrixEvaluationEquiv R d c (Localization.Away L.det)
      (matrixOverlapCoordinates R L N) = localizedTransitionEntries L N := by
    ext i j
    exact matrixOverlapCoordinates_X R L N i j
  rw [he]
  exact localizedTransitionEntries_evaluate R L N f h

end FlagVarieties.Foundations.QuotientCharts
