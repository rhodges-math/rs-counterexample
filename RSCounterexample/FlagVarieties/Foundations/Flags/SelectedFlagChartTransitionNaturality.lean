import RSCounterexample.FlagVarieties.Foundations.Flags.SelectedFlagChartTransition
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedChartTransitionNaturality

/-! # Full-flag transitions commute with arbitrary scalar maps -/

noncomputable section
namespace FlagVarieties.Foundations.QuotientCharts
universe u
variable (R : Type u) [CommRing R] {n : ℕ}
  (a b : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)
  {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

theorem selectedFlagChartTransition_comp
    (k : MvPolynomial (FlagChartVariable n) R →ₐ[R] A)
    (h : ∀ j, IsUnit ((k.comp (selectedFlagChartVariables R j))
      (selectedPolynomialBlock R (a j) (b j)).det))
    (g : A →ₐ[R] B)
    (hg : ∀ j, IsUnit (((g.comp k).comp (selectedFlagChartVariables R j))
      (selectedPolynomialBlock R (a j) (b j)).det)) :
    g.comp (selectedFlagChartTransition R a b k h) =
      selectedFlagChartTransition R a b (g.comp k) hg := by
  apply selectedFlagChartEvaluation_ext R
  intro j
  rw [AlgHom.comp_assoc, selectedFlagChartTransition_variables,
    selectedFlagChartTransition_variables]
  exact (selectedChartTransitionHom_comp R (a j) (b j)
    (k.comp (selectedFlagChartVariables R j)) g (h j) (hg j)).symm

end FlagVarieties.Foundations.QuotientCharts
