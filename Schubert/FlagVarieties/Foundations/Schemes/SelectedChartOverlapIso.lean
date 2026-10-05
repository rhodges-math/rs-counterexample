import Schubert.FlagVarieties.Foundations.Schemes.SelectedChartOverlapReturn

/-!
# Isomorphisms between the determinant overlaps

The regular map on a selected-chart overlap lands in the reverse overlap.
It lifts to its determinant localization, and the two lifted algebra maps
are inverse. Taking spectra gives a scheme isomorphism.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory

universe u

variable (R : Type u) [CommRing R]

theorem awayLiftAlgHom_algebraMap {P : Type u} [CommRing P] [Algebra R P] (x : P)
    (h : IsUnit (IsScalarTower.toAlgHom R P (Localization.Away x) x)) :
    (IsLocalization.Away.liftAlgHom x h : Localization.Away x →ₐ[R] Localization.Away x) =
      AlgHom.id R (Localization.Away x) := by
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers x)
  ext p
  simp

variable {n d : ℕ} (a b : Fin d ↪ Fin n)

theorem selectedChartTransitionHom_algebraMap
    (h : IsUnit ((IsScalarTower.toAlgHom R (MvPolynomial (Fin d × Fin (n - d)) R)
      (Localization.Away (selectedPolynomialBlock R a b).det))
        (selectedPolynomialBlock R a b).det)) :
    selectedChartTransitionHom R a b
      (IsScalarTower.toAlgHom R (MvPolynomial (Fin d × Fin (n - d)) R)
        (Localization.Away (selectedPolynomialBlock R a b).det)) h =
      matrixOverlapCoordinates R (selectedPolynomialBlock R a b)
        (remainingPolynomialBlock R a b) := by
  unfold selectedChartTransitionHom
  rw [awayLiftAlgHom_algebraMap, AlgHom.id_comp]

/-- The universal regular transition inverts the reverse selected determinant. -/
theorem selectedOverlapCoordinates_reverse_unit :
    IsUnit (matrixOverlapCoordinates R (selectedPolynomialBlock R a b)
      (remainingPolynomialBlock R a b)
      (selectedPolynomialBlock R b a).det) := by
  have h := selectedChartTransitionHom_reverse_unit R a b
    (IsScalarTower.toAlgHom R (MvPolynomial (Fin d × Fin (n - d)) R)
      (Localization.Away (selectedPolynomialBlock R a b).det))
    (IsLocalization.Away.algebraMap_isUnit (selectedPolynomialBlock R a b).det)
  have he := selectedChartTransitionHom_algebraMap R a b
    (IsLocalization.Away.algebraMap_isUnit (selectedPolynomialBlock R a b).det)
  exact (congrArg (fun q => IsUnit (q (selectedPolynomialBlock R b a).det)) he).mp h

/-- The lifted coordinate map from the reverse determinant localization. -/
def selectedOverlapLift :
    Localization.Away (selectedPolynomialBlock R b a).det →ₐ[R]
      Localization.Away (selectedPolynomialBlock R a b).det :=
  IsLocalization.Away.liftAlgHom (selectedPolynomialBlock R b a).det
    (selectedOverlapCoordinates_reverse_unit R a b)

@[simp] theorem selectedOverlapLift_algebraMap (p : MvPolynomial (Fin d × Fin (n - d)) R) :
    selectedOverlapLift R a b
      (algebraMap _ (Localization.Away (selectedPolynomialBlock R b a).det) p) =
      matrixOverlapCoordinates R (selectedPolynomialBlock R a b)
        (remainingPolynomialBlock R a b) p := by
  simp [selectedOverlapLift]

/-- Returning on the polynomial coordinate ring is the canonical localization map. -/
theorem selectedOverlapLift_coordinates :
    (selectedOverlapLift R a b).comp
      (matrixOverlapCoordinates R (selectedPolynomialBlock R b a)
        (remainingPolynomialBlock R b a)) =
      IsScalarTower.toAlgHom R (MvPolynomial (Fin d × Fin (n - d)) R)
        (Localization.Away (selectedPolynomialBlock R a b).det) := by
  let f := IsScalarTower.toAlgHom R (MvPolynomial (Fin d × Fin (n - d)) R)
    (Localization.Away (selectedPolynomialBlock R a b).det)
  have h : IsUnit (f (selectedPolynomialBlock R a b).det) :=
    IsLocalization.Away.algebraMap_isUnit (selectedPolynomialBlock R a b).det
  have hr := selectedChartTransitionHom_roundtrip R a b f h
    (selectedChartTransitionHom_reverse_unit R a b f h)
  have hf : selectedChartTransitionHom R a b f h =
      matrixOverlapCoordinates R (selectedPolynomialBlock R a b) (remainingPolynomialBlock R a b) :=
    selectedChartTransitionHom_algebraMap R a b h
  simp only [hf] at hr
  exact hr

theorem selectedOverlapLift_comp :
    (selectedOverlapLift R a b).comp (selectedOverlapLift R b a) =
      AlgHom.id R (Localization.Away (selectedPolynomialBlock R a b).det) := by
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (selectedPolynomialBlock R a b).det)
  apply RingHom.ext
  intro p
  change selectedOverlapLift R a b (selectedOverlapLift R b a
    (algebraMap _ (Localization.Away (selectedPolynomialBlock R a b).det) p)) = _
  rw [selectedOverlapLift_algebraMap]
  exact DFunLike.congr_fun (selectedOverlapLift_coordinates R a b) p

/-- The two localized overlap coordinate rings are isomorphic as base algebras. -/
def selectedOverlapAlgEquiv :
    Localization.Away (selectedPolynomialBlock R b a).det ≃ₐ[R]
      Localization.Away (selectedPolynomialBlock R a b).det :=
  AlgEquiv.ofAlgHom (selectedOverlapLift R a b) (selectedOverlapLift R b a)
    (selectedOverlapLift_comp R a b) (selectedOverlapLift_comp R b a)

/-- The affine determinant overlaps are isomorphic as schemes. -/
def selectedChartOverlapIso :
    Spec (CommRingCat.of (Localization.Away (selectedPolynomialBlock R a b).det)) ≅
      Spec (CommRingCat.of (Localization.Away (selectedPolynomialBlock R b a).det)) :=
  Scheme.Spec.mapIso (selectedOverlapAlgEquiv R a b).toRingEquiv.toCommRingCatIso.op

end FlagVarieties.Foundations.QuotientCharts
