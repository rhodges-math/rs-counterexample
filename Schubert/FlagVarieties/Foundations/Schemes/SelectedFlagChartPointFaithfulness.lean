import Schubert.FlagVarieties.Foundations.Schemes.SelectedFlagChartPointMaps
import Schubert.FlagVarieties.Foundations.Schemes.SelectedChartPointFaithfulness
import Schubert.FlagVarieties.Foundations.Flags.SelectedFlagChartRecovery

/-!
# The glued affine flag presentations identify exactly the same original flags

Equality of every quotient gives the determinant overlap and its
unique regular transition. Conversely, the global Grassmannian projections
detect every quotient step. Both implications concern scheme maps.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] {n : ℕ}
  (a b : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)
  {A : Type u} [CommRing A] [Algebra R A]
  (k l : MvPolynomial (FlagChartVariable n) R →ₐ[R] A)
  (hk : selectedFlagIncidenceIdeal R a ≤ RingHom.ker k.toRingHom)
  (hl : selectedFlagIncidenceIdeal R b ≤ RingHom.ker l.toRingHom)

theorem selectedFlagChartPointMap_eq_of_steps_eq
    (hs : ∀ j, selectedFlagChartStep R a k j = selectedFlagChartStep R b l j) :
    selectedFlagChartPointMap R a k hk = selectedFlagChartPointMap R b l hl := by
  have hu : ∀ j, IsUnit ((k.comp (selectedFlagChartVariables R j))
      (selectedPolynomialBlock R (a j) (b j)).det) := by
    intro j
    apply (selectedPolynomialBlock_open_iff R (a j) (b j) _ _
      (selectedChartPoint_presented R (a j) (k.comp (selectedFlagChartVariables R j)))).mpr
    change Function.Bijective ((selectedFlagChartStep R a k j).toSubmodule.mkQ.comp
      (coordinateInclusion (b j)))
    rw [hs j]
    exact selectedChartPoint_selected_bijective R (b j) _
  have ht : selectedFlagChartTransition R a b k hu = l := by
    apply selectedFlagChartStep_injective R b
    funext j
    exact (selectedFlagChartTransition_step R a b k hu j).trans (hs j)
  have hm := selectedFlagChartPointMap_transition R a b k hk hu
  simpa only [ht] using hm

theorem selectedFlagChartPointMap_steps_eq_of_eq
    (h : selectedFlagChartPointMap R a k hk = selectedFlagChartPointMap R b l hl)
    (j : Fin (n+1)) : selectedFlagChartStep R a k j = selectedFlagChartStep R b l j := by
  have hj := congrArg (fun f => f ≫ selectedFlagChartSchemeStep R n j) h
  rw [selectedFlagChartPointMap_step, selectedFlagChartPointMap_step] at hj
  exact selectedChartPoint_quotient_eq_of_map_eq R (a j) (b j) _ _ hj

theorem selectedFlagChartPointMap_eq_iff_steps_eq :
    selectedFlagChartPointMap R a k hk = selectedFlagChartPointMap R b l hl ↔
      ∀ j, selectedFlagChartStep R a k j = selectedFlagChartStep R b l j :=
  ⟨fun h j => selectedFlagChartPointMap_steps_eq_of_eq R a b k l hk hl h j,
    selectedFlagChartPointMap_eq_of_steps_eq R a b k l hk hl⟩

/-- No additional identifications of original RingFlags are introduced by scheme gluing. -/
theorem selectedFlagChartPointMap_eq_iff_ringFlag_eq :
    selectedFlagChartPointMap R a k hk = selectedFlagChartPointMap R b l hl ↔
      selectedFlagChartRingFlag R a k hk = selectedFlagChartRingFlag R b l hl := by
  rw [selectedFlagChartPointMap_eq_iff_steps_eq]
  constructor
  · intro h
    apply RingFlag.ext
    intro j
    exact congrArg Module.Grassmannian.toSubmodule (h j)
  · intro h j
    exact congrArg (fun F => F.step j) h

end FlagVarieties.Foundations.QuotientCharts
