import RSCounterexample.FlagVarieties.Foundations.Flags.SelectedFlagChartOverlap

/-!
# Evaluations of the full-flag determinant overlap

Any joint parameters satisfying incidence and the selected determinant
unit conditions extend uniquely to the localized incidence ring.
-/

noncomputable section
namespace FlagVarieties.Foundations.QuotientCharts
universe u
variable (R : Type u) [CommRing R] {n : ℕ}
  (a b : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)
  {A : Type u} [CommRing A] [Algebra R A]

/-- The `R`-algebra map out of the incidence ring of the chart `a` induced by chart coordinates `k`
that vanish on the incidence ideal. -/
def selectedFlagIncidenceEvaluation
    (k : MvPolynomial (FlagChartVariable n) R →ₐ[R] A)
    (hk : selectedFlagIncidenceIdeal R a ≤ RingHom.ker k.toRingHom) :
    (MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R a) →ₐ[R] A :=
  Ideal.Quotient.liftₐ (selectedFlagIncidenceIdeal R a) k (fun _ hp => hk hp)

@[simp]
theorem selectedFlagIncidenceEvaluation_mk
    (k : MvPolynomial (FlagChartVariable n) R →ₐ[R] A)
    (hk : selectedFlagIncidenceIdeal R a ≤ RingHom.ker k.toRingHom)
    (p : MvPolynomial (FlagChartVariable n) R) :
    selectedFlagIncidenceEvaluation R a k hk (Ideal.Quotient.mk _ p) = k p := rfl

theorem selectedFlagIncidenceEvaluation_unit
    (k : MvPolynomial (FlagChartVariable n) R →ₐ[R] A)
    (hk : selectedFlagIncidenceIdeal R a ≤ RingHom.ker k.toRingHom)
    (h : ∀ j, IsUnit ((k.comp (selectedFlagChartVariables R j))
      (selectedPolynomialBlock R (a j) (b j)).det)) :
    IsUnit (selectedFlagIncidenceEvaluation R a k hk (selectedFlagOverlapDeterminant R a b)) := by
  change IsUnit (k (selectedFlagOverlapPolynomial R a b))
  rw [selectedFlagOverlapPolynomial, map_prod]
  exact IsUnit.prod_univ_iff.mpr h

/-- The `R`-algebra map out of the overlap ring of the charts `a` and `b` induced by chart
coordinates `k` of `a` that vanish on the incidence ideal and invert the minors selected by `b`. -/
def selectedFlagOverlapEvaluation
    (k : MvPolynomial (FlagChartVariable n) R →ₐ[R] A)
    (hk : selectedFlagIncidenceIdeal R a ≤ RingHom.ker k.toRingHom)
    (h : ∀ j, IsUnit ((k.comp (selectedFlagChartVariables R j))
      (selectedPolynomialBlock R (a j) (b j)).det)) : SelectedFlagOverlapRing R a b →ₐ[R] A :=
  IsLocalization.Away.liftAlgHom (selectedFlagOverlapDeterminant R a b)
    (selectedFlagIncidenceEvaluation_unit R a b k hk h)

@[simp]
theorem selectedFlagOverlapEvaluation_algebraMap
    (k : MvPolynomial (FlagChartVariable n) R →ₐ[R] A)
    (hk : selectedFlagIncidenceIdeal R a ≤ RingHom.ker k.toRingHom)
    (h : ∀ j, IsUnit ((k.comp (selectedFlagChartVariables R j))
      (selectedPolynomialBlock R (a j) (b j)).det))
    (p : MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R a) :
    selectedFlagOverlapEvaluation R a b k hk h
      (algebraMap _ (SelectedFlagOverlapRing R a b) p) =
      selectedFlagIncidenceEvaluation R a k hk p := by
  simp [selectedFlagOverlapEvaluation]

theorem selectedFlagOverlapEvaluation_point
    (k : MvPolynomial (FlagChartVariable n) R →ₐ[R] A)
    (hk : selectedFlagIncidenceIdeal R a ≤ RingHom.ker k.toRingHom)
    (h : ∀ j, IsUnit ((k.comp (selectedFlagChartVariables R j))
      (selectedPolynomialBlock R (a j) (b j)).det)) :
    (selectedFlagOverlapEvaluation R a b k hk h).comp (selectedFlagOverlapPoint R a b) = k := by
  apply AlgHom.ext
  intro p
  change selectedFlagOverlapEvaluation R a b k hk h
    (algebraMap _ (SelectedFlagOverlapRing R a b)
      (Ideal.Quotient.mk (selectedFlagIncidenceIdeal R a) p)) = k p
  rw [selectedFlagOverlapEvaluation_algebraMap, selectedFlagIncidenceEvaluation_mk]

/-- Original joint coordinates determine every map out of the overlap ring. -/
theorem selectedFlagOverlapEvaluation_ext
    {f g : SelectedFlagOverlapRing R a b →ₐ[R] A}
    (h : f.comp (selectedFlagOverlapPoint R a b) = g.comp (selectedFlagOverlapPoint R a b)) :
    f = g := by
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (selectedFlagOverlapDeterminant R a b))
  apply RingHom.ext
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact AlgHom.congr_fun h p

end FlagVarieties.Foundations.QuotientCharts
