import Schubert.FlagVarieties.Foundations.Schemes.SelectedQuotientCoverBaseChange
import Schubert.FlagVarieties.Foundations.Flags.SelectedFlagChartRecovery

/-!
# Simultaneous principal coordinate cover of a ring flag

Choose a derived selected-quotient cover at every step of the given
flag. Products of their denominators give a common principal refinement. The
quotient steps and their kernels remain those of the original flag.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory

universe u

variable {A : Type u} [CommRing A] {n : ℕ}
  (F : RingFlag A (Fin n → A) n)

/-- The independently derived cover of the original quotient at step `j`. -/
def flagStepCover (j : Fin (n + 1)) :
    SelectedQuotientCover A A (F.step j) :=
  selectedQuotientCover A A (F.step j)

/-- One choice of a selected presentation at every step. -/
abbrev SimultaneousFlagCoordinateIndex :=
  (j : Fin (n + 1)) → (flagStepCover F j).index

/-- The common principal-open denominator of a simultaneous choice. -/
def simultaneousFlagCoordinateElement (i : SimultaneousFlagCoordinateIndex F) : A :=
  ∏ j : Fin (n + 1), (flagStepCover F j).element (i j)

/-- The original ambient coordinate selection at each step. -/
def simultaneousFlagCoordinateSelection (i : SimultaneousFlagCoordinateIndex F)
    (j : Fin (n + 1)) : Fin (n - j.val) ↪ Fin n :=
  (flagStepCover F j).selection (i j)

/-- Each chosen step denominator divides the common one. -/
theorem simultaneousFlagCoordinateElement_dvd
    (i : SimultaneousFlagCoordinateIndex F) (j : Fin (n + 1)) :
    (flagStepCover F j).element (i j) ∣ simultaneousFlagCoordinateElement F i := by
  unfold simultaneousFlagCoordinateElement
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ j)

/-- The product denominators give a principal cover of the whole spectrum. -/
theorem simultaneousFlagCoordinateElement_span_top :
    Ideal.span (Set.range (simultaneousFlagCoordinateElement F)) = ⊤ := by
  classical
  apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp
  apply top_le_iff.mp
  intro p _
  have hstep (j : Fin (n + 1)) :
      ∃ i : (flagStepCover F j).index,
        (flagStepCover F j).element i ∉ p.asIdeal := by
    have hc : (⨆ i, PrimeSpectrum.basicOpen ((flagStepCover F j).element i)) = ⊤ :=
      PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr (flagStepCover F j).span_top
    have hp : p ∈ ⨆ i, PrimeSpectrum.basicOpen ((flagStepCover F j).element i) := by
      rw [hc]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
    exact ⟨i, hi⟩
  choose i hi using hstep
  apply TopologicalSpace.Opens.mem_iSup.mpr
  refine ⟨i, ?_⟩
  change simultaneousFlagCoordinateElement F i ∉ p.asIdeal
  intro hp
  obtain ⟨j, _, hj⟩ := Ideal.IsPrime.prod_mem_iff.mp hp
  exact hi j hj

/-- Open cover by the simultaneous principal localization domains. -/
abbrev simultaneousFlagCoordinateSchemeCover : (Spec (CommRingCat.of A)).OpenCover :=
  (Scheme.affineOpenCoverOfSpanRangeEqTop
    (R := CommRingCat.of A) (simultaneousFlagCoordinateElement F)
    (simultaneousFlagCoordinateElement_span_top F)).openCover

end FlagVarieties.Foundations.QuotientCharts
