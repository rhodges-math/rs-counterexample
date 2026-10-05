import Schubert.FlagVarieties.Foundations.Flags.SelectedFlagChartOverlap
import Schubert.FlagVarieties.Foundations.Flags.SelectedFlagChartTransitionNaturality

/-! # Lifting the regular full-flag transition to both determinant opens -/

noncomputable section
namespace FlagVarieties.Foundations.QuotientCharts
universe u
variable (R : Type u) [CommRing R] {n : ℕ}
  (a b : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)

theorem selectedFlagOverlapCoordinates_reverse_unit :
    IsUnit (selectedFlagOverlapCoordinates R a b (selectedFlagOverlapDeterminant R b a)) := by
  change IsUnit (selectedFlagOverlapCoordinates R a b
    (Ideal.Quotient.mk (selectedFlagIncidenceIdeal R b) (selectedFlagOverlapPolynomial R b a)))
  rw [selectedFlagOverlapCoordinates_mk, selectedFlagOverlapPolynomial, map_prod]
  apply IsUnit.prod_univ_iff.mpr
  intro j
  exact selectedFlagChartTransition_reverse_unit R a b (selectedFlagOverlapPoint R a b)
    (selectedFlagOverlapPoint_unit R a b) j

/-- The regular map from the reverse overlap ring to the source overlap ring. -/
def selectedFlagOverlapLift : SelectedFlagOverlapRing R b a →ₐ[R] SelectedFlagOverlapRing R a b :=
  IsLocalization.Away.liftAlgHom (selectedFlagOverlapDeterminant R b a)
    (selectedFlagOverlapCoordinates_reverse_unit R a b)

@[simp]
theorem selectedFlagOverlapLift_algebraMap
    (p : MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R b) :
    selectedFlagOverlapLift R a b (algebraMap _ (SelectedFlagOverlapRing R b a) p) =
      selectedFlagOverlapCoordinates R a b p := by
  simp [selectedFlagOverlapLift]

theorem selectedFlagOverlapLift_point :
    (selectedFlagOverlapLift R a b).comp (selectedFlagOverlapPoint R b a) =
      selectedFlagChartTransition R a b (selectedFlagOverlapPoint R a b)
        (selectedFlagOverlapPoint_unit R a b) := by
  apply AlgHom.ext
  intro p
  change selectedFlagOverlapLift R a b
    (algebraMap _ (SelectedFlagOverlapRing R b a)
      (Ideal.Quotient.mk (selectedFlagIncidenceIdeal R b) p)) = _
  rw [selectedFlagOverlapLift_algebraMap, selectedFlagOverlapCoordinates_mk]

/-- Returning to the original coordinates is the original localization map. -/
theorem selectedFlagOverlapLift_transition :
    (selectedFlagOverlapLift R a b).comp
      (selectedFlagChartTransition R b a (selectedFlagOverlapPoint R b a)
        (selectedFlagOverlapPoint_unit R b a)) = selectedFlagOverlapPoint R a b := by
  have hu : ∀ j, IsUnit ((((selectedFlagOverlapLift R a b).comp
      (selectedFlagOverlapPoint R b a)).comp (selectedFlagChartVariables R j))
        (selectedPolynomialBlock R (b j) (a j)).det) := by
    intro j
    exact (selectedFlagOverlapPoint_unit R b a j).map (selectedFlagOverlapLift R a b)
  rw [selectedFlagChartTransition_comp R b a _ _ _ hu]
  simp only [selectedFlagOverlapLift_point]
  apply selectedFlagChartTransition_roundtrip

theorem selectedFlagOverlapLift_coordinates :
    (selectedFlagOverlapLift R a b).comp (selectedFlagOverlapCoordinates R b a) =
      IsScalarTower.toAlgHom R
        (MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R a)
        (SelectedFlagOverlapRing R a b) := by
  apply AlgHom.ext
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  change selectedFlagOverlapLift R a b (selectedFlagOverlapCoordinates R b a
    (Ideal.Quotient.mk (selectedFlagIncidenceIdeal R a) p)) = _
  rw [selectedFlagOverlapCoordinates_mk]
  exact AlgHom.congr_fun (selectedFlagOverlapLift_transition R a b) p

end FlagVarieties.Foundations.QuotientCharts
