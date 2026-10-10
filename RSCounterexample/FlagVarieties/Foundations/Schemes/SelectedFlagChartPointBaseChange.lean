import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedFlagChartPointMaps
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedQuotientCoverBaseChange

/-! # Base equations and scalar extension for affine flag-chart maps -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] {n : ℕ}
  (a : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)
  {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  (k : MvPolynomial (FlagChartVariable n) R →ₐ[R] A)
  (hk : selectedFlagIncidenceIdeal R a ≤ RingHom.ker k.toRingHom)

@[reassoc]
theorem selectedFlagChartPointMap_toSpec :
    selectedFlagChartPointMap R a k hk ≫ selectedFlagChartSchemeToSpec R n =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  rw [selectedFlagChartPointMap, Category.assoc, selectedFlagChartSchemeChart_toSpec]
  exact spec_map_algHom_toSpec R (selectedFlagIncidenceEvaluation R a k hk)

include hk in
theorem selectedFlagIncidenceIdeal_comp (g : A →ₐ[R] B) :
    selectedFlagIncidenceIdeal R a ≤ RingHom.ker (g.comp k).toRingHom := by
  intro p hp
  change g (k p) = 0
  rw [show k p = 0 from hk hp, map_zero]

@[reassoc]
theorem selectedFlagChartPointMap_comp (g : A →ₐ[R] B) :
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ selectedFlagChartPointMap R a k hk =
      selectedFlagChartPointMap R a (g.comp k) (selectedFlagIncidenceIdeal_comp R a k hk g) := by
  have he : g.comp (selectedFlagIncidenceEvaluation R a k hk) =
      selectedFlagIncidenceEvaluation R a (g.comp k)
        (selectedFlagIncidenceIdeal_comp R a k hk g) := by
    apply AlgHom.ext
    intro z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    rfl
  unfold selectedFlagChartPointMap
  rw [← Category.assoc, spec_map_algHom_comp, he]

end FlagVarieties.Foundations.QuotientCharts
