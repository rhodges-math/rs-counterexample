import RSCounterexample.FlagVarieties.Foundations.Flags.SelectedFlagChartTransition
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedChartOverlapCompatibility

/-!
# Inverse and cocycle laws for regular full-flag transitions

All statements are equalities of algebra maps. Unit conditions for the
reverse and composite transitions follow from the original determinants.
-/

noncomputable section
namespace FlagVarieties.Foundations.QuotientCharts
universe u
variable (R : Type u) [CommRing R] {n : ℕ}
  (a b c : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)
  {A : Type u} [CommRing A] [Algebra R A]
  (k : MvPolynomial (FlagChartVariable n) R →ₐ[R] A)

theorem selectedFlagChartTransition_reverse_unit
    (h : ∀ j, IsUnit ((k.comp (selectedFlagChartVariables R j))
      (selectedPolynomialBlock R (a j) (b j)).det)) (j : Fin (n+1)) :
    IsUnit (((selectedFlagChartTransition R a b k h).comp
      (selectedFlagChartVariables R j)) (selectedPolynomialBlock R (b j) (a j)).det) := by
  rw [selectedFlagChartTransition_variables]
  exact selectedChartTransitionHom_reverse_unit R (a j) (b j) _ (h j)

theorem selectedFlagChartTransition_roundtrip
    (h : ∀ j, IsUnit ((k.comp (selectedFlagChartVariables R j))
      (selectedPolynomialBlock R (a j) (b j)).det))
    (hback : ∀ j, IsUnit (((selectedFlagChartTransition R a b k h).comp
      (selectedFlagChartVariables R j)) (selectedPolynomialBlock R (b j) (a j)).det)) :
    selectedFlagChartTransition R b a (selectedFlagChartTransition R a b k h) hback = k := by
  apply selectedFlagChartEvaluation_ext R
  intro j
  simp only [selectedFlagChartTransition_variables]
  apply selectedChartTransitionHom_roundtrip

theorem selectedFlagChartTransition_trans_unit
    (hab : ∀ j, IsUnit ((k.comp (selectedFlagChartVariables R j))
      (selectedPolynomialBlock R (a j) (b j)).det))
    (hbc : ∀ j, IsUnit (((selectedFlagChartTransition R a b k hab).comp
      (selectedFlagChartVariables R j)) (selectedPolynomialBlock R (b j) (c j)).det))
    (j : Fin (n+1)) :
    IsUnit ((k.comp (selectedFlagChartVariables R j))
      (selectedPolynomialBlock R (a j) (c j)).det) := by
  apply selectedChartTransitionHom_trans_unit R (a j) (b j) (c j) _ (hab j)
  simpa only [selectedFlagChartTransition_variables] using hbc j

theorem selectedFlagChartTransition_trans
    (hab : ∀ j, IsUnit ((k.comp (selectedFlagChartVariables R j))
      (selectedPolynomialBlock R (a j) (b j)).det))
    (hbc : ∀ j, IsUnit (((selectedFlagChartTransition R a b k hab).comp
      (selectedFlagChartVariables R j)) (selectedPolynomialBlock R (b j) (c j)).det))
    (hac : ∀ j, IsUnit ((k.comp (selectedFlagChartVariables R j))
      (selectedPolynomialBlock R (a j) (c j)).det)) :
    selectedFlagChartTransition R b c (selectedFlagChartTransition R a b k hab) hbc =
      selectedFlagChartTransition R a c k hac := by
  apply selectedFlagChartEvaluation_ext R
  intro j
  simp only [selectedFlagChartTransition_variables]
  apply selectedChartTransitionHom_trans

end FlagVarieties.Foundations.QuotientCharts
