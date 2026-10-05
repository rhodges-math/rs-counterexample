import Schubert.FlagVarieties.Foundations.Flags.SelectedFlagTripleOverlapCoordinates
import Schubert.FlagVarieties.Foundations.Flags.SelectedFlagOverlapEvaluation

/-! # The map from the second-third overlap ring to the triple ring -/

noncomputable section
namespace FlagVarieties.Foundations.QuotientCharts
universe u
variable (R : Type u) [CommRing R] {n : ℕ}
  (a b c : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)

/-- The map from the overlap ring of the charts `b` and `c` to the triple overlap ring, through the
coordinates of `b`. -/
def selectedFlagTripleOverlapToSecondThird :
    SelectedFlagOverlapRing R b c →ₐ[R] SelectedFlagTripleOverlapRing R a b c :=
  selectedFlagOverlapEvaluation R b c (selectedFlagTripleOverlapSecond R a b c)
    (selectedFlagTripleOverlapSecond_ideal R a b c) (selectedFlagTripleOverlapSecond_unit R a b c)

theorem selectedFlagTripleOverlapToSecondThird_point :
    (selectedFlagTripleOverlapToSecondThird R a b c).comp (selectedFlagOverlapPoint R b c) =
      selectedFlagTripleOverlapSecond R a b c :=
  selectedFlagOverlapEvaluation_point R b c _ _ _

theorem selectedFlagTripleOverlapLeft_transition :
    (selectedFlagTripleOverlapLeft R a b c).comp
      (selectedFlagChartTransition R a b (selectedFlagOverlapPoint R a b)
        (selectedFlagOverlapPoint_unit R a b)) = selectedFlagTripleOverlapSecond R a b c := by
  have hu := fun j => (selectedFlagOverlapPoint_unit R a b j).map
    (selectedFlagTripleOverlapLeft R a b c)
  have h := selectedFlagChartTransition_comp R a b (selectedFlagOverlapPoint R a b)
    (selectedFlagOverlapPoint_unit R a b) (selectedFlagTripleOverlapLeft R a b c) hu
  simpa only [selectedFlagTripleOverlapLeft_restrict, selectedFlagTripleOverlapSecond] using h

theorem selectedFlagTripleOverlapToSecondThird_first :
    (selectedFlagTripleOverlapToSecondThird R a b c).comp
      (IsScalarTower.toAlgHom R
        (MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R b)
        (SelectedFlagOverlapRing R b c)) =
    (selectedFlagTripleOverlapLeft R a b c).comp (selectedFlagOverlapCoordinates R a b) := by
  apply AlgHom.ext
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  change selectedFlagOverlapEvaluation R b c (selectedFlagTripleOverlapSecond R a b c)
    (selectedFlagTripleOverlapSecond_ideal R a b c) (selectedFlagTripleOverlapSecond_unit R a b c)
    (algebraMap _ (SelectedFlagOverlapRing R b c)
      (Ideal.Quotient.mk (selectedFlagIncidenceIdeal R b) p)) = _
  rw [selectedFlagOverlapEvaluation_algebraMap, selectedFlagIncidenceEvaluation_mk]
  change _ = selectedFlagTripleOverlapLeft R a b c
    (selectedFlagOverlapCoordinates R a b (Ideal.Quotient.mk (selectedFlagIncidenceIdeal R b) p))
  rw [selectedFlagOverlapCoordinates_mk]
  exact (AlgHom.congr_fun (selectedFlagTripleOverlapLeft_transition R a b c) p).symm

theorem selectedFlagTripleOverlapToSecondThird_transition :
    (selectedFlagTripleOverlapToSecondThird R a b c).comp
      (selectedFlagChartTransition R b c (selectedFlagOverlapPoint R b c)
        (selectedFlagOverlapPoint_unit R b c)) =
    selectedFlagChartTransition R a c (selectedFlagTripleOverlapPoint R a b c)
      (selectedFlagTripleOverlap_right_unit R a b c) := by
  have hu := fun j => (selectedFlagOverlapPoint_unit R b c j).map
    (selectedFlagTripleOverlapToSecondThird R a b c)
  have h := selectedFlagChartTransition_comp R b c (selectedFlagOverlapPoint R b c)
    (selectedFlagOverlapPoint_unit R b c) (selectedFlagTripleOverlapToSecondThird R a b c) hu
  simp only [selectedFlagTripleOverlapToSecondThird_point] at h
  exact h.trans (selectedFlagTripleOverlap_trans R a b c)

theorem selectedFlagTripleOverlapRight_transition :
    (selectedFlagTripleOverlapRight R a b c).comp
      (selectedFlagChartTransition R a c (selectedFlagOverlapPoint R a c)
        (selectedFlagOverlapPoint_unit R a c)) =
    selectedFlagChartTransition R a c (selectedFlagTripleOverlapPoint R a b c)
      (selectedFlagTripleOverlap_right_unit R a b c) := by
  have hu := fun j => (selectedFlagOverlapPoint_unit R a c j).map
    (selectedFlagTripleOverlapRight R a b c)
  have h := selectedFlagChartTransition_comp R a c (selectedFlagOverlapPoint R a c)
    (selectedFlagOverlapPoint_unit R a c) (selectedFlagTripleOverlapRight R a b c) hu
  simpa only [selectedFlagTripleOverlapRight_restrict] using h

theorem selectedFlagTripleOverlapToSecondThird_third :
    (selectedFlagTripleOverlapToSecondThird R a b c).comp (selectedFlagOverlapCoordinates R b c) =
      (selectedFlagTripleOverlapRight R a b c).comp (selectedFlagOverlapCoordinates R a c) := by
  apply AlgHom.ext
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  change selectedFlagTripleOverlapToSecondThird R a b c
    (selectedFlagOverlapCoordinates R b c (Ideal.Quotient.mk (selectedFlagIncidenceIdeal R c) p)) =
    selectedFlagTripleOverlapRight R a b c
      (selectedFlagOverlapCoordinates R a c (Ideal.Quotient.mk (selectedFlagIncidenceIdeal R c) p))
  rw [selectedFlagOverlapCoordinates_mk, selectedFlagOverlapCoordinates_mk]
  exact AlgHom.congr_fun ((selectedFlagTripleOverlapToSecondThird_transition R a b c).trans
    (selectedFlagTripleOverlapRight_transition R a b c).symm) p

end FlagVarieties.Foundations.QuotientCharts
