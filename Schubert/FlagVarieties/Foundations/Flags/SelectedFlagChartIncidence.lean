import Schubert.FlagVarieties.Foundations.Flags.SelectedFlagChartParameters

/-!
# Adjacent incidence equations in the joint full-flag parameter ring

The pair-incidence equations are inserted in their original two sets of
variables. Vanishing is equivalent to nesting those adjacent
quotient kernels, over any commutative coefficient algebra.
-/

noncomputable section
namespace FlagVarieties.Foundations.QuotientCharts
universe u
variable (R : Type u) [CommRing R] {n : ℕ}
  (a : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)

/-- Insert both sets of adjacent quotient parameters in the full flag ring. -/
def selectedFlagChartAdjacentVariables (j : Fin n) :
    MvPolynomial ((Fin (n-j.castSucc.val) × Fin (n-(n-j.castSucc.val))) ⊕
      (Fin (n-j.succ.val) × Fin (n-(n-j.succ.val)))) R →ₐ[R]
      MvPolynomial (FlagChartVariable n) R :=
  MvPolynomial.rename (Sum.elim (fun x => ⟨j.castSucc, x⟩) (fun x => ⟨j.succ, x⟩))

@[simp]
theorem selectedFlagChartAdjacentVariables_left (j : Fin n) :
    (selectedFlagChartAdjacentVariables R j).comp (MvPolynomial.rename Sum.inl) =
      selectedFlagChartVariables R j.castSucc := by
  ext x
  simp [selectedFlagChartAdjacentVariables, selectedFlagChartVariables]

@[simp]
theorem selectedFlagChartAdjacentVariables_right (j : Fin n) :
    (selectedFlagChartAdjacentVariables R j).comp (MvPolynomial.rename Sum.inr) =
      selectedFlagChartVariables R j.succ := by
  ext x
  simp [selectedFlagChartAdjacentVariables, selectedFlagChartVariables]

/-- An adjacent-incidence equation in the full flag parameter ring. -/
def selectedFlagIncidencePolynomial (j : Fin n) (i : Fin (n-j.succ.val)) (c : Fin n) :
    MvPolynomial (FlagChartVariable n) R :=
  selectedFlagChartAdjacentVariables R j
    (selectedIncidencePolynomial R (a j.castSucc) (a j.succ) i c)

theorem selectedFlagIncidencePolynomial_vanish_iff
    {A : Type u} [CommRing A] [Algebra R A]
    (k : MvPolynomial (FlagChartVariable n) R →ₐ[R] A) (j : Fin n) :
    (∀ (i : Fin (n-j.succ.val)) (c : Fin n),
      k (selectedFlagIncidencePolynomial R a j i c) = 0) ↔
      (selectedFlagChartStep R a k j.castSucc).toSubmodule ≤
        (selectedFlagChartStep R a k j.succ).toSubmodule := by
  have h := selectedIncidencePolynomial_vanish_iff R (a j.castSucc) (a j.succ)
    (k.comp (selectedFlagChartAdjacentVariables R j))
  simpa only [AlgHom.comp_assoc, selectedFlagChartAdjacentVariables_left,
    selectedFlagChartAdjacentVariables_right, AlgHom.comp_apply,
    selectedFlagIncidencePolynomial, selectedFlagChartStep] using h

/-- Adjacent equations impose all inclusions, with no further compatibility premise. -/
theorem selectedFlagIncidencePolynomial_all_vanish_iff
    {A : Type u} [CommRing A] [Algebra R A]
    (k : MvPolynomial (FlagChartVariable n) R →ₐ[R] A) :
    (∀ (j : Fin n) (i : Fin (n-j.succ.val)) (c : Fin n),
      k (selectedFlagIncidencePolynomial R a j i c) = 0) ↔
      Monotone (fun j => (selectedFlagChartStep R a k j).toSubmodule) := by
  simp only [Fin.monotone_iff_le_succ, selectedFlagIncidencePolynomial_vanish_iff]

end FlagVarieties.Foundations.QuotientCharts
