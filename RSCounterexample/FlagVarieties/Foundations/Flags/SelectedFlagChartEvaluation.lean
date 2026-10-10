import RSCounterexample.FlagVarieties.Foundations.Flags.SelectedFlagChartParameters

/-!
# Evaluating the joint full-flag parameters

An algebra map out of the joint parameter ring is exactly a family of maps
out of the original quotient-chart rings. The inverse laws retain every
labelled coordinate; in particular they can compare regular transition maps.
-/

noncomputable section
namespace FlagVarieties.Foundations.QuotientCharts
universe u
variable (R : Type u) [CommRing R] {n : ℕ}
  {A : Type u} [CommRing A] [Algebra R A]

/-- Combine the evaluations of all quotient steps in one algebra map. -/
def selectedFlagChartEvaluation
    (f : (j : Fin (n+1)) →
      MvPolynomial (Fin (n-j.val) × Fin (n-(n-j.val))) R →ₐ[R] A) :
    MvPolynomial (FlagChartVariable n) R →ₐ[R] A :=
  MvPolynomial.aeval (fun x => f x.1 (MvPolynomial.X x.2))

@[simp]
theorem selectedFlagChartEvaluation_variables
    (f : (j : Fin (n+1)) →
      MvPolynomial (Fin (n-j.val) × Fin (n-(n-j.val))) R →ₐ[R] A)
    (j : Fin (n+1)) :
    (selectedFlagChartEvaluation R f).comp (selectedFlagChartVariables R j) = f j := by
  ext x
  simp [selectedFlagChartEvaluation, selectedFlagChartVariables]

/-- Equality on the original quotient-chart rings determines the joint map. -/
theorem selectedFlagChartEvaluation_ext
    {f g : MvPolynomial (FlagChartVariable n) R →ₐ[R] A}
    (h : ∀ j, f.comp (selectedFlagChartVariables R j) =
      g.comp (selectedFlagChartVariables R j)) : f = g := by
  ext x
  rcases x with ⟨j, x⟩
  have hx := AlgHom.congr_fun (h j) (MvPolynomial.X x)
  simpa [selectedFlagChartVariables] using hx

@[simp]
theorem selectedFlagChartEvaluation_restrict
    (f : MvPolynomial (FlagChartVariable n) R →ₐ[R] A) :
    selectedFlagChartEvaluation R
      (fun j => f.comp (selectedFlagChartVariables R j)) = f := by
  apply selectedFlagChartEvaluation_ext R
  intro j
  exact selectedFlagChartEvaluation_variables R _ j

/-- The joint parameters are precisely the independent step parameters. -/
def selectedFlagChartEvaluationEquiv :
    (MvPolynomial (FlagChartVariable n) R →ₐ[R] A) ≃
      ((j : Fin (n+1)) →
        MvPolynomial (Fin (n-j.val) × Fin (n-(n-j.val))) R →ₐ[R] A) where
  toFun f j := f.comp (selectedFlagChartVariables R j)
  invFun := selectedFlagChartEvaluation R
  left_inv := selectedFlagChartEvaluation_restrict R
  right_inv f := funext (selectedFlagChartEvaluation_variables R f)

end FlagVarieties.Foundations.QuotientCharts
