import RSCounterexample.FlagVarieties.Foundations.Flags.SelectedFlagChartOverlapLift
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Joint parameters on the tensor-product triple-overlap ring

The two overlap rings are tensored over their common incidence chart ring.
Their universal full-flag parameters agree, and the regular transition to
the second chart lies in the determinant open for the third chart.
-/

noncomputable section
namespace FlagVarieties.Foundations.QuotientCharts
open TensorProduct
universe u
variable (R : Type u) [CommRing R] {n : ℕ}
  (a b c : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)

/-- The coordinate ring of the triple overlap of the charts `a`, `b`, `c`: the overlap rings of
`(a, b)` and `(a, c)`, tensored over the incidence ring of `a`. -/
abbrev SelectedFlagTripleOverlapRing :=
  SelectedFlagOverlapRing R a b ⊗[
    MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R a]
      SelectedFlagOverlapRing R a c

/-- The map from the overlap ring of the charts `a` and `b` to the triple overlap ring. -/
def selectedFlagTripleOverlapLeft :
    SelectedFlagOverlapRing R a b →ₐ[R] SelectedFlagTripleOverlapRing R a b c :=
  Algebra.TensorProduct.includeLeft

/-- The map from the overlap ring of the charts `a` and `c` to the triple overlap ring. -/
def selectedFlagTripleOverlapRight :
    SelectedFlagOverlapRing R a c →ₐ[R] SelectedFlagTripleOverlapRing R a b c :=
  (Algebra.TensorProduct.includeRight : SelectedFlagOverlapRing R a c →ₐ[
    MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R a]
      SelectedFlagTripleOverlapRing R a b c).restrictScalars R

/-- The coordinates of the chart `a` on the triple overlap. -/
def selectedFlagTripleOverlapPoint :
    MvPolynomial (FlagChartVariable n) R →ₐ[R] SelectedFlagTripleOverlapRing R a b c :=
  (IsScalarTower.toAlgHom R
    (MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R a)
    (SelectedFlagTripleOverlapRing R a b c)).comp (Ideal.Quotient.mkₐ R _)

theorem selectedFlagTripleOverlapLeft_restrict :
    (selectedFlagTripleOverlapLeft R a b c).comp (selectedFlagOverlapPoint R a b) =
      selectedFlagTripleOverlapPoint R a b c := by
  apply AlgHom.ext
  intro p
  rfl

theorem selectedFlagTripleOverlapRight_restrict :
    (selectedFlagTripleOverlapRight R a b c).comp (selectedFlagOverlapPoint R a c) =
      selectedFlagTripleOverlapPoint R a b c := by
  apply AlgHom.ext
  intro p
  exact (Algebra.TensorProduct.includeRight : SelectedFlagOverlapRing R a c →ₐ[
    MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R a]
      SelectedFlagTripleOverlapRing R a b c).commutes (Ideal.Quotient.mk _ p)

theorem selectedFlagTripleOverlapPoint_ideal : selectedFlagIncidenceIdeal R a ≤
    RingHom.ker (selectedFlagTripleOverlapPoint R a b c).toRingHom := by
  intro p hp
  change algebraMap _ (SelectedFlagTripleOverlapRing R a b c)
    (Ideal.Quotient.mk (selectedFlagIncidenceIdeal R a) p) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]

theorem selectedFlagTripleOverlap_left_unit (j : Fin (n+1)) :
    IsUnit (((selectedFlagTripleOverlapPoint R a b c).comp (selectedFlagChartVariables R j))
      (selectedPolynomialBlock R (a j) (b j)).det) := by
  have h := (selectedFlagOverlapPoint_unit R a b j).map (selectedFlagTripleOverlapLeft R a b c)
  simpa only [← AlgHom.comp_apply, ← AlgHom.comp_assoc,
    selectedFlagTripleOverlapLeft_restrict] using h

theorem selectedFlagTripleOverlap_right_unit (j : Fin (n+1)) :
    IsUnit (((selectedFlagTripleOverlapPoint R a b c).comp (selectedFlagChartVariables R j))
      (selectedPolynomialBlock R (a j) (c j)).det) := by
  have h := (selectedFlagOverlapPoint_unit R a c j).map (selectedFlagTripleOverlapRight R a b c)
  simpa only [← AlgHom.comp_apply, ← AlgHom.comp_assoc,
    selectedFlagTripleOverlapRight_restrict] using h

/-- The coordinates of the chart `b` on the triple overlap, obtained from those of `a` by the chart
transition. -/
def selectedFlagTripleOverlapSecond :
    MvPolynomial (FlagChartVariable n) R →ₐ[R] SelectedFlagTripleOverlapRing R a b c :=
  selectedFlagChartTransition R a b (selectedFlagTripleOverlapPoint R a b c)
    (selectedFlagTripleOverlap_left_unit R a b c)

theorem selectedFlagTripleOverlapSecond_ideal : selectedFlagIncidenceIdeal R b ≤
    RingHom.ker (selectedFlagTripleOverlapSecond R a b c).toRingHom :=
  selectedFlagChartTransition_ideal R a b _ _ (selectedFlagTripleOverlapPoint_ideal R a b c)

theorem selectedFlagTripleOverlapSecond_unit (j : Fin (n+1)) :
    IsUnit (((selectedFlagTripleOverlapSecond R a b c).comp (selectedFlagChartVariables R j))
      (selectedPolynomialBlock R (b j) (c j)).det) := by
  unfold selectedFlagTripleOverlapSecond
  rw [selectedFlagChartTransition_variables]
  exact selectedChartTransitionHom_joint_unit R (a j) (b j) (c j) _
    (selectedFlagTripleOverlap_left_unit R a b c j) (selectedFlagTripleOverlap_right_unit R a b c j)

theorem selectedFlagTripleOverlap_trans :
    selectedFlagChartTransition R b c (selectedFlagTripleOverlapSecond R a b c)
      (selectedFlagTripleOverlapSecond_unit R a b c) =
    selectedFlagChartTransition R a c (selectedFlagTripleOverlapPoint R a b c)
      (selectedFlagTripleOverlap_right_unit R a b c) :=
  selectedFlagChartTransition_trans R a b c _ _ _ _

end FlagVarieties.Foundations.QuotientCharts
