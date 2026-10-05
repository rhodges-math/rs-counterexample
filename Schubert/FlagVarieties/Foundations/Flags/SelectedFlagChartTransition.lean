import Schubert.FlagVarieties.Foundations.Flags.SelectedFlagChartEvaluation
import Schubert.FlagVarieties.Foundations.Flags.SelectedFlagChartIdeal
import Schubert.FlagVarieties.Foundations.Schemes.SelectedPresentationTransition

/-!
# Regular changes of all selected flag coordinates

The stepwise regular transitions combine to an algebra map on the
joint parameters. They preserve every original quotient kernel and hence
the full incidence ideal, over any commutative coefficient algebra.
-/

noncomputable section
namespace FlagVarieties.Foundations.QuotientCharts
universe u
variable (R : Type u) [CommRing R] {n : ℕ}
  (a b : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)
  {A : Type u} [CommRing A] [Algebra R A]
  (k : MvPolynomial (FlagChartVariable n) R →ₐ[R] A)

/-- The simultaneous determinant-open regular change of flag coordinates. -/
def selectedFlagChartTransition
    (h : ∀ j, IsUnit ((k.comp (selectedFlagChartVariables R j))
      (selectedPolynomialBlock R (a j) (b j)).det)) :
    MvPolynomial (FlagChartVariable n) R →ₐ[R] A :=
  selectedFlagChartEvaluation R (fun j =>
    selectedChartTransitionHom R (a j) (b j)
      (k.comp (selectedFlagChartVariables R j)) (h j))

@[simp]
theorem selectedFlagChartTransition_variables
    (h : ∀ j, IsUnit ((k.comp (selectedFlagChartVariables R j))
      (selectedPolynomialBlock R (a j) (b j)).det)) (j : Fin (n+1)) :
    (selectedFlagChartTransition R a b k h).comp (selectedFlagChartVariables R j) =
      selectedChartTransitionHom R (a j) (b j)
        (k.comp (selectedFlagChartVariables R j)) (h j) :=
  selectedFlagChartEvaluation_variables R _ j

/-- Every step is the same quotient, with its original ambient coordinates. -/
theorem selectedFlagChartTransition_step
    (h : ∀ j, IsUnit ((k.comp (selectedFlagChartVariables R j))
      (selectedPolynomialBlock R (a j) (b j)).det)) (j : Fin (n+1)) :
    selectedFlagChartStep R b (selectedFlagChartTransition R a b k h) j =
      selectedFlagChartStep R a k j := by
  unfold selectedFlagChartStep
  rw [selectedFlagChartTransition_variables]
  exact (selectedChartPoint_transition R (a j) (b j) _ (h j)).symm

/-- Incidence is preserved as an identity over arbitrary rings, not just fields. -/
theorem selectedFlagChartTransition_ideal
    (h : ∀ j, IsUnit ((k.comp (selectedFlagChartVariables R j))
      (selectedPolynomialBlock R (a j) (b j)).det))
    (hk : selectedFlagIncidenceIdeal R a ≤ RingHom.ker k.toRingHom) :
    selectedFlagIncidenceIdeal R b ≤
      RingHom.ker (selectedFlagChartTransition R a b k h).toRingHom := by
  rw [selectedFlagIncidenceIdeal_le_ker_iff] at hk ⊢
  simpa only [selectedFlagChartTransition_step] using hk

/-- Consequently the regular transition factors through the target incidence ring. -/
def selectedFlagChartTransitionFactor
    (h : ∀ j, IsUnit ((k.comp (selectedFlagChartVariables R j))
      (selectedPolynomialBlock R (a j) (b j)).det))
    (hk : selectedFlagIncidenceIdeal R a ≤ RingHom.ker k.toRingHom) :
    (MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R b) →ₐ[R] A :=
  Ideal.Quotient.liftₐ (selectedFlagIncidenceIdeal R b)
    (selectedFlagChartTransition R a b k h)
    (fun _ hp => selectedFlagChartTransition_ideal R a b k h hk hp)

@[simp]
theorem selectedFlagChartTransitionFactor_comp
    (h : ∀ j, IsUnit ((k.comp (selectedFlagChartVariables R j))
      (selectedPolynomialBlock R (a j) (b j)).det))
    (hk : selectedFlagIncidenceIdeal R a ≤ RingHom.ker k.toRingHom) :
    (selectedFlagChartTransitionFactor R a b k h hk).comp
      (Ideal.Quotient.mkₐ R (selectedFlagIncidenceIdeal R b)) =
        selectedFlagChartTransition R a b k h :=
  Ideal.Quotient.liftₐ_comp _ _ _

end FlagVarieties.Foundations.QuotientCharts
