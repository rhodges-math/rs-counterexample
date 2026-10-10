import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedFlagIncidenceChart
import RSCounterexample.FlagVarieties.Foundations.Schemes.QuotientFlagFamilyPullback
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedPresentationSheaf

/-!
# Quotient-sheaf flag on the full incidence chart

The quotient ring of the adjacent incidence equations carries, at every
step, the original normalized selected matrix quotient of the labelled
free sheaf. The adjacent factor maps are the forced maps from the
selected-coordinate sections, and their source equations hold over the
whole (possibly nonreduced) incidence chart.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u

variable (R : Type u) [CommRing R] {n : ℕ}
  (a : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)

/-- The coordinate ring of the complete incidence chart. -/
abbrev selectedFlagIncidenceRing :=
  MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R a

/-- The original matrix parameters for one step in the incidence ring. -/
def selectedFlagIncidenceStepEval (j : Fin (n+1)) :
    MvPolynomial (Fin (n-j.val) × Fin (n-(n-j.val))) R →ₐ[R]
      selectedFlagIncidenceRing R a :=
  (Ideal.Quotient.mkₐ R (selectedFlagIncidenceIdeal R a)).comp
    (selectedFlagChartVariables R j)

/-- Adjacent matrix quotients factor in the prescribed direction. -/
theorem selectedFlagIncidenceStep_factor (j : Fin n) :
    ((selectedPresentationMap R (a j.succ)
      (selectedFlagIncidenceStepEval R a j.succ)).comp
        (coordinateInclusion (a j.castSucc))).comp
      (selectedPresentationMap R (a j.castSucc)
        (selectedFlagIncidenceStepEval R a j.castSucc)) =
      selectedPresentationMap R (a j.succ)
        (selectedFlagIncidenceStepEval R a j.succ) := by
  have hk : selectedFlagIncidenceIdeal R a ≤
      RingHom.ker (Ideal.Quotient.mkₐ R (selectedFlagIncidenceIdeal R a)).toRingHom :=
    fun p hp => Ideal.Quotient.eq_zero_iff_mem.mpr hp
  have hmono := (selectedFlagIncidenceIdeal_le_ker_iff R a _).mp hk
  exact (selectedChartPoint_le_iff_factor R (a j.castSucc) (a j.succ)
    (selectedFlagIncidenceStepEval R a j.castSucc)
    (selectedFlagIncidenceStepEval R a j.succ)).mp
    (hmono (show j.castSucc ≤ j.succ from Nat.le_succ j.val))

/-- The labelled free-sheaf quotient at one flag step. -/
def selectedFlagIncidenceSheafQuotient (j : Fin (n+1)) :
    coordinateFreeSheaf (selectedFlagIncidenceChart R a) n ⟶
      coordinateFreeSheaf (selectedFlagIncidenceChart R a) (n-j.val) :=
  selectedPresentationSheafMap R
    (CommRingCat.of (selectedFlagIncidenceRing R a)) (a j)
    (selectedFlagIncidenceStepEval R a j)

/-- The forced adjacent factor of the matrix quotient sheaves. -/
def selectedFlagIncidenceSheafTransition (j : Fin n) :
    coordinateFreeSheaf (selectedFlagIncidenceChart R a) (n-j.castSucc.val) ⟶
      coordinateFreeSheaf (selectedFlagIncidenceChart R a) (n-j.succ.val) :=
  selectedPresentationSheafSection
      (CommRingCat.of (selectedFlagIncidenceRing R a)) (a j.castSucc) ≫
    selectedFlagIncidenceSheafQuotient R a j.succ

@[reassoc]
theorem selectedFlagIncidenceSheafTransition_source (j : Fin n) :
    selectedFlagIncidenceSheafQuotient R a j.castSucc ≫
      selectedFlagIncidenceSheafTransition R a j =
      selectedFlagIncidenceSheafQuotient R a j.succ := by
  unfold selectedFlagIncidenceSheafTransition selectedFlagIncidenceSheafQuotient
  simp only [selectedPresentationSheafMap, selectedPresentationSheafSection,
    Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (tilde.map _) (tilde.map _), ← tilde.map_comp,
    ← ModuleCat.ofHom_comp]
  rw [← Category.assoc (tilde.map _) (tilde.map _), ← tilde.map_comp,
    ← ModuleCat.ofHom_comp]
  have hf := selectedFlagIncidenceStep_factor R a j
  rw [LinearMap.comp_assoc] at hf
  rw [hf]

/-- The incidence chart carries a complete family of quotient
sheaves with its normalized matrices and adjacent factors. -/
def selectedFlagIncidenceSheafFamily :
    QuotientFlagFamily (selectedFlagIncidenceChart R a) n where
  target j := coordinateFreeSheaf (selectedFlagIncidenceChart R a) (n-j.val)
  quotient j := selectedFlagIncidenceSheafQuotient R a j
  quotient_epi j := by
    change Epi (selectedPresentationSheafMap R
      (CommRingCat.of (selectedFlagIncidenceRing R a)) (a j)
      (selectedFlagIncidenceStepEval R a j))
    infer_instance
  local_frames j x :=
    ⟨⊤, by simp, ⟨FlagVarieties.Foundations.ModuleSheafGluing.coordinateOverFreeIso ⊤ (n-j.val)⟩⟩
  transition j := selectedFlagIncidenceSheafTransition R a j
  transition_source j := selectedFlagIncidenceSheafTransition_source R a j

end FlagVarieties.Foundations.QuotientCharts
