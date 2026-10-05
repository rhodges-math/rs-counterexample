import Schubert.FlagVarieties.Foundations.Flags.SelectedFlagChartTransitionLaws

/-!
# The universal determinant overlap of two full-flag incidence charts

We localize the incidence quotient by the product of the selected
determinants. The stepwise regular maps therefore define a morphism to
the target incidence chart on this entire ring, including nilpotents.
-/

noncomputable section
namespace FlagVarieties.Foundations.QuotientCharts
universe u
variable (R : Type u) [CommRing R] {n : ℕ}
  (a b : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)

/-- The product imposing simultaneous availability of the new selected coordinates. -/
def selectedFlagOverlapPolynomial : MvPolynomial (FlagChartVariable n) R :=
  ∏ j, selectedFlagChartVariables R j (selectedPolynomialBlock R (a j) (b j)).det

/-- The determinant product in the source incidence quotient. -/
def selectedFlagOverlapDeterminant :
    MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R a :=
  Ideal.Quotient.mk _ (selectedFlagOverlapPolynomial R a b)

/-- The coordinate ring of the simultaneous flag-chart overlap. -/
abbrev SelectedFlagOverlapRing := Localization.Away (selectedFlagOverlapDeterminant R a b)

/-- Its universal full-flag parameter evaluation. -/
def selectedFlagOverlapPoint :
    MvPolynomial (FlagChartVariable n) R →ₐ[R] SelectedFlagOverlapRing R a b :=
  (IsScalarTower.toAlgHom R
    (MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R a)
    (SelectedFlagOverlapRing R a b)).comp (Ideal.Quotient.mkₐ R _)

theorem selectedFlagOverlapPoint_ideal : selectedFlagIncidenceIdeal R a ≤
    RingHom.ker (selectedFlagOverlapPoint R a b).toRingHom := by
  intro p hp
  change algebraMap _ (SelectedFlagOverlapRing R a b)
    (Ideal.Quotient.mk (selectedFlagIncidenceIdeal R a) p) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]

theorem selectedFlagOverlapPoint_unit (j : Fin (n+1)) :
    IsUnit (((selectedFlagOverlapPoint R a b).comp (selectedFlagChartVariables R j))
      (selectedPolynomialBlock R (a j) (b j)).det) := by
  have h : IsUnit (selectedFlagOverlapPoint R a b (selectedFlagOverlapPolynomial R a b)) :=
    IsLocalization.Away.algebraMap_isUnit (selectedFlagOverlapDeterminant R a b)
  rw [selectedFlagOverlapPolynomial, map_prod] at h
  exact (IsUnit.prod_univ_iff.mp h) j

/-- The target incidence ring maps regularly into the source overlap ring. -/
def selectedFlagOverlapCoordinates :
    (MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R b) →ₐ[R]
      SelectedFlagOverlapRing R a b :=
  selectedFlagChartTransitionFactor R a b (selectedFlagOverlapPoint R a b)
    (selectedFlagOverlapPoint_unit R a b) (selectedFlagOverlapPoint_ideal R a b)

@[simp]
theorem selectedFlagOverlapCoordinates_mk (p : MvPolynomial (FlagChartVariable n) R) :
    selectedFlagOverlapCoordinates R a b (Ideal.Quotient.mk _ p) =
      selectedFlagChartTransition R a b (selectedFlagOverlapPoint R a b)
        (selectedFlagOverlapPoint_unit R a b) p := rfl

end FlagVarieties.Foundations.QuotientCharts
