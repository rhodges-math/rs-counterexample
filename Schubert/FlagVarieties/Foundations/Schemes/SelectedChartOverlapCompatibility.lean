import Schubert.FlagVarieties.Foundations.Schemes.SelectedChartOverlapIso

/-!
# Compatibility of the regular selected-chart overlaps

The overlap isomorphism followed by the inclusion into the second affine
matrix chart is exactly the previously constructed regular transition.
At every algebra-valued point, two successive transitions give the direct
transition, and applicability of the direct transition is a conclusion.
The scheme maps on triple intersections are
`Schemes/SelectedTripleOverlapMaps.lean`, and the gluing data are
`Schemes/SelectedChartGlueData.lean`.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory

universe u

variable (R : Type u) [CommRing R] {n d : ℕ} (a b : Fin d ↪ Fin n)

theorem selectedChartOverlapIso_hom :
    (selectedChartOverlapIso R a b).hom =
      Spec.map (CommRingCat.ofHom (selectedOverlapLift R a b).toRingHom) := rfl

/-- The lifted overlap isomorphism gives the same morphism to the
second affine chart as the universal inverse-block construction. -/
theorem selectedChartOverlapIso_hom_chart :
    (selectedChartOverlapIso R a b).hom ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap (MvPolynomial (Fin d × Fin (n - d)) R)
          (Localization.Away (selectedPolynomialBlock R b a).det))) =
      selectedChartOverlapMap R a b := by
  rw [selectedChartOverlapIso_hom, ← Spec.map_comp]
  change Spec.map _ = Spec.map _
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  exact selectedOverlapLift_algebraMap R a b p

variable {A : Type u} [CommRing A] [Algebra R A] (c : Fin d ↪ Fin n)

/-- Applicability on two consecutive overlaps implies applicability on
the direct overlap of the starting quotient. -/
theorem selectedChartTransitionHom_trans_unit
    (f : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A)
    (hab : IsUnit (f (selectedPolynomialBlock R a b).det))
    (hbc : IsUnit (selectedChartTransitionHom R a b f hab (selectedPolynomialBlock R b c).det)) :
    IsUnit (f (selectedPolynomialBlock R a c).det) := by
  apply (selectedPolynomialBlock_open_iff R a c f _ (selectedChartPoint_presented R a f)).mpr
  exact (selectedPolynomialBlock_open_iff R b c _ _
    (selectedChartTransitionHom_represents R a b f hab _
      (selectedChartPoint_presented R a f))).mp hbc

/-- The exact triple transition law as polynomial algebra-map equality,
uniformly over every commutative base algebra. -/
theorem selectedChartTransitionHom_trans
    (f : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A)
    (hab : IsUnit (f (selectedPolynomialBlock R a b).det))
    (hbc : IsUnit (selectedChartTransitionHom R a b f hab (selectedPolynomialBlock R b c).det))
    (hac : IsUnit (f (selectedPolynomialBlock R a c).det)) :
    selectedChartTransitionHom R b c (selectedChartTransitionHom R a b f hab) hbc =
      selectedChartTransitionHom R a c f hac := by
  apply (matrixEvaluationEquiv R d (n - d) A).injective
  apply matrixGrassmannianChartEquiv.injective
  apply Subtype.ext
  exact (selectedChartTransitionHom_represents R b c _ hbc (selectedChartPoint R a f)
    (selectedChartTransitionHom_represents R a b f hab _
      (selectedChartPoint_presented R a f))).trans
      (selectedChartTransitionHom_represents R a c f hac _
        (selectedChartPoint_presented R a f)).symm

end FlagVarieties.Foundations.QuotientCharts
