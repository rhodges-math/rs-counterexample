import RSCounterexample.FlagVarieties.Foundations.Flags.SelectedFlagChartIncidence

/-!
# The full flag incidence ring and its universal flag

The ideal consists of adjacent incidence equations. Its quotient carries
the existing RingFlag, with selected-chart kernels as its steps,
all inclusions proved, and the zero and full endpoints proved separately.
-/

noncomputable section
namespace FlagVarieties.Foundations.QuotientCharts
universe u
variable (R : Type u) [CommRing R] {n : ℕ}
  (a : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)

/-- One index for each adjacent-incidence equation. -/
abbrev FlagIncidenceEquationIndex (n : ℕ) :=
  (j : Fin n) × (Fin (n-j.succ.val) × Fin n)

/-- The full flag incidence ideal in the joint parameter ring. -/
def selectedFlagIncidenceIdeal : Ideal (MvPolynomial (FlagChartVariable n) R) :=
  Ideal.span (Set.range (fun p : FlagIncidenceEquationIndex n =>
    selectedFlagIncidencePolynomial R a p.1 p.2.1 p.2.2))

theorem selectedFlagIncidenceIdeal_le_ker_iff
    {A : Type u} [CommRing A] [Algebra R A]
    (k : MvPolynomial (FlagChartVariable n) R →ₐ[R] A) :
    selectedFlagIncidenceIdeal R a ≤ RingHom.ker k.toRingHom ↔
      Monotone (fun j => (selectedFlagChartStep R a k j).toSubmodule) := by
  rw [← selectedFlagIncidencePolynomial_all_vanish_iff]
  constructor
  · intro h j i c
    exact h (Ideal.subset_span ⟨⟨j, i, c⟩, rfl⟩)
  · intro h
    apply Ideal.span_le.mpr
    rintro p ⟨⟨j, i, c⟩, rfl⟩
    exact h j i c

/-- Joint parameters satisfying the ideal define a full ring-valued flag. -/
def selectedFlagChartRingFlag {A : Type u} [CommRing A] [Algebra R A]
    (k : MvPolynomial (FlagChartVariable n) R →ₐ[R] A)
    (hk : selectedFlagIncidenceIdeal R a ≤ RingHom.ker k.toRingHom) :
    RingFlag A (Fin n → A) n where
  step := selectedFlagChartStep R a k
  step_mono := (selectedFlagIncidenceIdeal_le_ker_iff R a k).mp hk
  step_zero := selectedFlagChartStep_zero R a k
  step_last := selectedFlagChartStep_last R a k

@[simp]
theorem selectedFlagChartRingFlag_step {A : Type u} [CommRing A] [Algebra R A]
    (k : MvPolynomial (FlagChartVariable n) R →ₐ[R] A)
    (hk : selectedFlagIncidenceIdeal R a ≤ RingHom.ker k.toRingHom) (j : Fin (n+1)) :
    (selectedFlagChartRingFlag R a k hk).step j = selectedFlagChartStep R a k j := rfl

/-- The original kernels form the universal full flag over the incidence ring. -/
def selectedFlagChartUniversal :
    RingFlag (MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R a)
      (Fin n → (MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R a)) n :=
  selectedFlagChartRingFlag R a (Ideal.Quotient.mkₐ R (selectedFlagIncidenceIdeal R a))
    (fun _p hp => Ideal.Quotient.eq_zero_iff_mem.mpr hp)

end FlagVarieties.Foundations.QuotientCharts
