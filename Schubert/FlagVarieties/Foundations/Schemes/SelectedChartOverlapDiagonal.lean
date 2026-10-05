import Schubert.FlagVarieties.Foundations.Schemes.SelectedChartOverlapCompatibility
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# The overlap inclusions and diagonal identities

The determinant localization maps are open immersions. On a diagonal
overlap the selected coordinates are already a quotient basis, so the
determinant is a unit and the inclusion is an isomorphism. The
overlap transition is the identity there, as required by scheme gluing.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory

universe u

variable (R : Type u) [CommRing R] {n d : ℕ} (a b : Fin d ↪ Fin n)

/-- The canonical immersion of a determinant overlap in its first chart. -/
def selectedChartOverlapInclusion :
    Spec (CommRingCat.of (Localization.Away (selectedPolynomialBlock R a b).det)) ⟶
      Spec (CommRingCat.of (MvPolynomial (Fin d × Fin (n - d)) R)) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (MvPolynomial (Fin d × Fin (n - d)) R)
      (Localization.Away (selectedPolynomialBlock R a b).det)))

instance selectedChartOverlapInclusion_open :
    IsOpenImmersion (selectedChartOverlapInclusion R a b) := by
  unfold selectedChartOverlapInclusion
  infer_instance

instance selectedChartOverlapMap_open : IsOpenImmersion (selectedChartOverlapMap R a b) := by
  rw [← selectedChartOverlapIso_hom_chart]
  infer_instance

/-- A selection is applicable to its own universal normalized quotient. -/
theorem selectedPolynomialBlock_diagonal_unit : IsUnit (selectedPolynomialBlock R a a).det := by
  exact (selectedPolynomialBlock_open_iff R a a (AlgHom.id _ _) _
    (selectedChartPoint_presented R a (AlgHom.id _ _))).mpr
      (selectedChartPoint_selected_bijective R a (AlgHom.id _ _))

instance selectedChartOverlapInclusion_diagonal_iso :
    IsIso (selectedChartOverlapInclusion R a a) := by
  let e := IsLocalization.atUnit (MvPolynomial (Fin d × Fin (n - d)) R)
    (Localization.Away (selectedPolynomialBlock R a a).det)
    (selectedPolynomialBlock R a a).det (selectedPolynomialBlock_diagonal_unit R a)
  have he : e.toRingEquiv.toCommRingCatIso.hom = CommRingCat.ofHom
      (algebraMap (MvPolynomial (Fin d × Fin (n - d)) R)
        (Localization.Away (selectedPolynomialBlock R a a).det)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    exact e.toAlgHom.commutes p
  unfold selectedChartOverlapInclusion
  rw [← he]
  infer_instance

variable {A : Type u} [CommRing A] [Algebra R A]

/-- The diagonal regular transition preserves every polynomial evaluation. -/
theorem selectedChartTransitionHom_self
    (f : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A)
    (h : IsUnit (f (selectedPolynomialBlock R a a).det)) :
    selectedChartTransitionHom R a a f h = f := by
  apply (matrixEvaluationEquiv R d (n - d) A).injective
  apply matrixGrassmannianChartEquiv.injective
  apply Subtype.ext
  exact (selectedChartTransitionHom_represents R a a f h _
    (selectedChartPoint_presented R a f)).trans (selectedChartPoint_presented R a f).symm

theorem selectedOverlapCoordinates_diagonal :
    matrixOverlapCoordinates R (selectedPolynomialBlock R a a) (remainingPolynomialBlock R a a) =
      IsScalarTower.toAlgHom R (MvPolynomial (Fin d × Fin (n - d)) R)
        (Localization.Away (selectedPolynomialBlock R a a).det) := by
  rw [← selectedChartTransitionHom_algebraMap R a a
    (IsLocalization.Away.algebraMap_isUnit (selectedPolynomialBlock R a a).det)]
  exact selectedChartTransitionHom_self R a _ _

theorem selectedChartOverlapIso_self : (selectedChartOverlapIso R a a).hom = 𝟙 _ := by
  have h : selectedOverlapLift R a a =
      AlgHom.id R (Localization.Away (selectedPolynomialBlock R a a).det) := by
    apply AlgHom.toRingHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers (selectedPolynomialBlock R a a).det)
    apply RingHom.ext
    intro p
    change selectedOverlapLift R a a
      (algebraMap _ (Localization.Away (selectedPolynomialBlock R a a).det) p) =
        algebraMap _ (Localization.Away (selectedPolynomialBlock R a a).det) p
    rw [selectedOverlapLift_algebraMap]
    exact DFunLike.congr_fun (selectedOverlapCoordinates_diagonal R a) p
  rw [selectedChartOverlapIso_hom, h]
  exact Scheme.Spec.map_id _

/-- The transition in the reverse direction is the inverse scheme map. -/
theorem selectedChartOverlapIso_reverse :
    (selectedChartOverlapIso R a b).hom ≫ (selectedChartOverlapIso R b a).hom = 𝟙 _ := by
  rw [selectedChartOverlapIso_hom, selectedChartOverlapIso_hom, ← Spec.map_comp]
  have h := selectedOverlapLift_comp R a b
  change Spec.map (CommRingCat.ofHom
    ((selectedOverlapLift R a b).comp (selectedOverlapLift R b a)).toRingHom) = _
  rw [h]
  exact Scheme.Spec.map_id _

end FlagVarieties.Foundations.QuotientCharts
