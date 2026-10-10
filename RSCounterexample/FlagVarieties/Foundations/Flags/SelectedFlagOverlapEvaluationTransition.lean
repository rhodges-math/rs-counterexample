import RSCounterexample.FlagVarieties.Foundations.Flags.SelectedFlagOverlapEvaluation
import RSCounterexample.FlagVarieties.Foundations.Flags.SelectedFlagChartTransitionNaturality

/-! # Evaluation of the regular transition on the flag overlap -/

noncomputable section
namespace FlagVarieties.Foundations.QuotientCharts
universe u
variable (R : Type u) [CommRing R] {n : ℕ}
  (a b : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)
  {A : Type u} [CommRing A] [Algebra R A]
  (k : MvPolynomial (FlagChartVariable n) R →ₐ[R] A)
  (hk : selectedFlagIncidenceIdeal R a ≤ RingHom.ker k.toRingHom)
  (h : ∀ j, IsUnit ((k.comp (selectedFlagChartVariables R j))
    (selectedPolynomialBlock R (a j) (b j)).det))

theorem selectedFlagOverlapEvaluation_coordinates :
    (selectedFlagOverlapEvaluation R a b k hk h).comp (selectedFlagOverlapCoordinates R a b) =
      selectedFlagIncidenceEvaluation R b (selectedFlagChartTransition R a b k h)
        (selectedFlagChartTransition_ideal R a b k h hk) := by
  have hu := fun j => (selectedFlagOverlapPoint_unit R a b j).map
    (selectedFlagOverlapEvaluation R a b k hk h)
  have ht := selectedFlagChartTransition_comp R a b (selectedFlagOverlapPoint R a b)
    (selectedFlagOverlapPoint_unit R a b) (selectedFlagOverlapEvaluation R a b k hk h) hu
  simp only [selectedFlagOverlapEvaluation_point] at ht
  apply AlgHom.ext
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  change selectedFlagOverlapEvaluation R a b k hk h
    (selectedFlagOverlapCoordinates R a b
      (Ideal.Quotient.mk (selectedFlagIncidenceIdeal R b) p)) = _
  rw [selectedFlagOverlapCoordinates_mk, selectedFlagIncidenceEvaluation_mk]
  exact AlgHom.congr_fun ht p

end FlagVarieties.Foundations.QuotientCharts
