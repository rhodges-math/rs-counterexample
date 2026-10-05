import Schubert.FlagVarieties.Foundations.Flags.SelectedFlagChartEndpoints
import Schubert.FlagVarieties.Foundations.Flags.Ring
import Schubert.FlagVarieties.Foundations.Flags.SelectedChartIncidencePolynomial

/-!
# Joint affine parameters for every step of a full flag

Every flag step retains its selected quotient chart and original ambient
coordinates. Variables are disjoint across steps, and the rank of the j-th
quotient is exactly n-j, as in the existing RingFlag definition.
-/

noncomputable section
namespace FlagVarieties.Foundations.QuotientCharts
universe u

/-- One variable for each entry in each selected quotient chart. -/
abbrev FlagChartVariable (n : ℕ) :=
  (j : Fin (n+1)) × (Fin (n-j.val) × Fin (n-(n-j.val)))

variable (R : Type u) [CommRing R] {n : ℕ}
  (a : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)
  {A : Type u} [CommRing A] [Algebra R A]

/-- Include the variables of one quotient step in the joint parameter ring. -/
def selectedFlagChartVariables (j : Fin (n+1)) :
    MvPolynomial (Fin (n-j.val) × Fin (n-(n-j.val))) R →ₐ[R]
      MvPolynomial (FlagChartVariable n) R :=
  MvPolynomial.rename (fun x => ⟨j, x⟩)

/-- The quotient kernel at step j of the joint parameter family. -/
def selectedFlagChartStep (k : MvPolynomial (FlagChartVariable n) R →ₐ[R] A)
    (j : Fin (n+1)) : Module.Grassmannian A (Fin n → A) (n-j.val) :=
  selectedChartPoint R (a j) (k.comp (selectedFlagChartVariables R j))

theorem selectedFlagChartStep_zero (k : MvPolynomial (FlagChartVariable n) R →ₐ[R] A) :
    (selectedFlagChartStep R a k 0).toSubmodule = ⊥ :=
  selectedChartPoint_full_bottom R (a 0) _

theorem selectedFlagChartStep_last (k : MvPolynomial (FlagChartVariable n) R →ₐ[R] A) :
    (selectedFlagChartStep R a k (Fin.last n)).toSubmodule = ⊤ := by
  unfold selectedFlagChartStep
  rw [← selectedPresentationMap_ker, LinearMap.ker_eq_top]
  ext v i
  have hi := i.isLt
  simp at hi

end FlagVarieties.Foundations.QuotientCharts
