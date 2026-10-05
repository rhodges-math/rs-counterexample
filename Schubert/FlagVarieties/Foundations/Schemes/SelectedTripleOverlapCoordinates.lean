import Schubert.FlagVarieties.Foundations.Schemes.SelectedChartTransitionNaturality
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Coordinate maps on the affine triple intersection

The tensor product of the two determinant localizations is the coordinate
ring of their fiber product over the first affine chart. Its two universal
points represent the same quotient. Hence the transition to the second
chart lies in its overlap with the third, and the two routes to the third
chart agree as algebra homomorphisms, including nilpotent base rings.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

open TensorProduct

universe u

variable (R : Type u) [CommRing R] {n d : ℕ} (a b c : Fin d ↪ Fin n)

/-- The tensor-product coordinate ring of the triple intersection. -/
abbrev selectedTripleOverlapRing :=
  Localization.Away (selectedPolynomialBlock R a b).det ⊗[
    MvPolynomial (Fin d × Fin (n - d)) R]
      Localization.Away (selectedPolynomialBlock R a c).det

/-- The first localization map into the fiber-product coordinate ring. -/
def selectedTripleOverlapLeft :
    Localization.Away (selectedPolynomialBlock R a b).det →ₐ[R]
      selectedTripleOverlapRing R a b c := Algebra.TensorProduct.includeLeft

/-- The second localization map, restricted to the original coefficient ring. -/
def selectedTripleOverlapRight :
    Localization.Away (selectedPolynomialBlock R a c).det →ₐ[R]
      selectedTripleOverlapRing R a b c :=
  (Algebra.TensorProduct.includeRight : Localization.Away (selectedPolynomialBlock R a c).det →ₐ[
    MvPolynomial (Fin d × Fin (n - d)) R] selectedTripleOverlapRing R a b c).restrictScalars R

/-- The common first-chart coordinate map on the triple intersection. -/
def selectedTripleOverlapPoint :
    MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] selectedTripleOverlapRing R a b c :=
  IsScalarTower.toAlgHom R (MvPolynomial (Fin d × Fin (n - d)) R)
    (selectedTripleOverlapRing R a b c)

theorem selectedTripleOverlapLeft_restrict :
    (selectedTripleOverlapLeft R a b c).comp
      (IsScalarTower.toAlgHom R (MvPolynomial (Fin d × Fin (n - d)) R)
        (Localization.Away (selectedPolynomialBlock R a b).det)) =
      selectedTripleOverlapPoint R a b c := by
  apply AlgHom.ext
  intro p
  rfl

theorem selectedTripleOverlapRight_restrict :
    (selectedTripleOverlapRight R a b c).comp
      (IsScalarTower.toAlgHom R (MvPolynomial (Fin d × Fin (n - d)) R)
        (Localization.Away (selectedPolynomialBlock R a c).det)) =
      selectedTripleOverlapPoint R a b c := by
  apply AlgHom.ext
  intro p
  exact (Algebra.TensorProduct.includeRight :
    Localization.Away (selectedPolynomialBlock R a c).det →ₐ[
      MvPolynomial (Fin d × Fin (n - d)) R] selectedTripleOverlapRing R a b c).commutes p

theorem selectedTripleOverlap_left_unit :
    IsUnit (selectedTripleOverlapPoint R a b c (selectedPolynomialBlock R a b).det) := by
  have h := (IsLocalization.Away.algebraMap_isUnit (selectedPolynomialBlock R a b).det).map
    (selectedTripleOverlapLeft R a b c)
  exact h

theorem selectedTripleOverlap_right_unit :
    IsUnit (selectedTripleOverlapPoint R a b c (selectedPolynomialBlock R a c).det) := by
  have h := (IsLocalization.Away.algebraMap_isUnit (selectedPolynomialBlock R a c).det).map
    (selectedTripleOverlapRight R a b c)
  have he := DFunLike.congr_fun (selectedTripleOverlapRight_restrict R a b c)
    (selectedPolynomialBlock R a c).det
  exact he ▸ h

/-- The second-chart point on the triple intersection. -/
def selectedTripleOverlapSecond :
    MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] selectedTripleOverlapRing R a b c :=
  selectedChartTransitionHom R a b (selectedTripleOverlapPoint R a b c)
    (selectedTripleOverlap_left_unit R a b c)

theorem selectedTripleOverlapSecond_eq :
    selectedTripleOverlapSecond R a b c =
      (selectedTripleOverlapLeft R a b c).comp
        (matrixOverlapCoordinates R (selectedPolynomialBlock R a b)
          (remainingPolynomialBlock R a b)) := by
  exact selectedChartTransitionHom_restriction R a b (selectedTripleOverlapLeft R a b c)
    (selectedTripleOverlap_left_unit R a b c)

theorem selectedTripleOverlap_second_unit :
    IsUnit (selectedTripleOverlapSecond R a b c (selectedPolynomialBlock R b c).det) :=
  selectedChartTransitionHom_joint_unit R a b c (selectedTripleOverlapPoint R a b c)
    (selectedTripleOverlap_left_unit R a b c) (selectedTripleOverlap_right_unit R a b c)

/-- The regular morphism to the second/third overlap, in the contravariant direction. -/
def selectedTripleOverlapLift :
    Localization.Away (selectedPolynomialBlock R b c).det →ₐ[R]
      selectedTripleOverlapRing R a b c :=
  IsLocalization.Away.liftAlgHom (selectedPolynomialBlock R b c).det
    (selectedTripleOverlap_second_unit R a b c)

@[simp] theorem selectedTripleOverlapLift_algebraMap
    (p : MvPolynomial (Fin d × Fin (n - d)) R) :
    selectedTripleOverlapLift R a b c
      (algebraMap _ (Localization.Away (selectedPolynomialBlock R b c).det) p) =
        selectedTripleOverlapSecond R a b c p := by
  simp [selectedTripleOverlapLift]

/-- Both regular routes to the third chart coincide on the triple intersection. -/
theorem selectedTripleOverlapLift_coordinates :
    (selectedTripleOverlapLift R a b c).comp
      (matrixOverlapCoordinates R (selectedPolynomialBlock R b c)
        (remainingPolynomialBlock R b c)) =
      (selectedTripleOverlapRight R a b c).comp
        (matrixOverlapCoordinates R (selectedPolynomialBlock R a c)
          (remainingPolynomialBlock R a c)) := by
  have h := selectedChartTransitionHom_trans R a b c (selectedTripleOverlapPoint R a b c)
    (selectedTripleOverlap_left_unit R a b c) (selectedTripleOverlap_second_unit R a b c)
      (selectedTripleOverlap_right_unit R a b c)
  have hr := selectedChartTransitionHom_restriction R a c (selectedTripleOverlapRight R a b c)
    (show IsUnit (((selectedTripleOverlapRight R a b c).comp
      (IsScalarTower.toAlgHom R (MvPolynomial (Fin d × Fin (n - d)) R)
        (Localization.Away (selectedPolynomialBlock R a c).det)))
          (selectedPolynomialBlock R a c).det) from
      (IsLocalization.Away.algebraMap_isUnit (selectedPolynomialBlock R a c).det).map
        (selectedTripleOverlapRight R a b c))
  simp only [selectedTripleOverlapRight_restrict] at hr
  exact h.trans hr

end FlagVarieties.Foundations.QuotientCharts
