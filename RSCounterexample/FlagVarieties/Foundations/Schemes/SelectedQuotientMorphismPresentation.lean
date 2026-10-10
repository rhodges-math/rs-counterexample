import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedQuotientMorphism

/-!
# The quotient morphism agrees with every global selected presentation

No global presentation is needed to define the morphism. If one is available,
the intrinsic construction agrees with the original normalized chart map.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {n d : ℕ} {P : Module.Grassmannian A (Fin n → A) d}

/-- A global presentation computes the quotient map constructed using arbitrary local charts. -/
theorem selectedQuotientMorphism_eq_pointMap (a : Fin d ↪ Fin n)
    (f : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A)
    (h : P = selectedChartPoint R a f) :
    selectedQuotientMorphism R P = selectedChartPointMap R a f := by
  let D := selectedQuotientCover R A P
  apply D.schemeCover.hom_ext
  intro i
  rw [D.ι_selectedQuotientMorphism]
  change selectedChartPointMap R (D.selection i) (D.evaluation i) =
    Spec.map (CommRingCat.ofHom
      (IsScalarTower.toAlgHom R A (Localization.Away (D.element i))).toRingHom) ≫
      selectedChartPointMap R a f
  rw [selectedChartPointMap_comp]
  apply selectedChartPointMap_eq_of_quotient_eq
  rw [D.represents]
  exact (congrArg (coordinateGrassmannianBaseChange (Localization.Away (D.element i))) h).trans
    (selectedChartPoint_baseChange_tower R a f)

/-- The intrinsic construction recovers the original affine chart map. -/
theorem selectedQuotientMorphism_selectedChartPoint (a : Fin d ↪ Fin n)
    (f : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A) :
    selectedQuotientMorphism R (selectedChartPoint R a f) = selectedChartPointMap R a f :=
  selectedQuotientMorphism_eq_pointMap a f rfl

end FlagVarieties.Foundations.QuotientCharts
