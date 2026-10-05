import Schubert.FlagVarieties.Foundations.Flags.SelectedChartParameterRecovery
import Schubert.FlagVarieties.Foundations.Flags.SelectedFlagChartEvaluation
import Schubert.FlagVarieties.Foundations.Flags.SelectedFlagChartIdeal

/-!
# Exact selected-chart parameters of an existing ring-valued flag

A chosen quotient basis at every step determines one joint parameter map.
Its incidence equations follow from the original flag inclusions, rather
than being an additional assumption on the flag.
-/

noncomputable section
namespace FlagVarieties.Foundations.QuotientCharts
universe u
variable (R : Type u) [CommRing R] {n : ℕ}
  {A : Type u} [CommRing A] [Algebra R A]
  (F : RingFlag A (Fin n → A) n)
  (a : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)

/-- Joint selected parameters are faithful to every original flag step. -/
theorem selectedFlagChartStep_injective :
    Function.Injective (fun k : MvPolynomial (FlagChartVariable n) R →ₐ[R] A =>
      selectedFlagChartStep R a k) := by
  intro k l h
  apply selectedFlagChartEvaluation_ext R
  intro j
  exact selectedChartPoint_injective R (a j) (congrFun h j)

/-- Applicable selected bases give unique parameters satisfying the entire incidence ideal. -/
theorem selectedFlagChart_existsUnique
    (ha : ∀ j, Function.Bijective ((F.step j).toSubmodule.mkQ.comp (coordinateInclusion (a j)))) :
    ∃! k : MvPolynomial (FlagChartVariable n) R →ₐ[R] A,
      selectedFlagIncidenceIdeal R a ≤ RingHom.ker k.toRingHom ∧
        ∀ j, selectedFlagChartStep R a k j = F.step j := by
  have hs : ∀ j, ∃ f : MvPolynomial (Fin (n-j.val) × Fin (n-(n-j.val))) R →ₐ[R] A,
      selectedChartPoint R (a j) f = F.step j := by
    intro j
    exact (selectedChartPoint_existsUnique R (a j) (F.step j) (ha j)).exists
  choose f hf using hs
  let k := selectedFlagChartEvaluation R f
  have hstep : ∀ j, selectedFlagChartStep R a k j = F.step j := by
    intro j
    unfold selectedFlagChartStep
    rw [selectedFlagChartEvaluation_variables]
    exact hf j
  have hk : selectedFlagIncidenceIdeal R a ≤ RingHom.ker k.toRingHom := by
    rw [selectedFlagIncidenceIdeal_le_ker_iff]
    simpa only [hstep] using F.step_mono
  refine ⟨k, ⟨hk, hstep⟩, ?_⟩
  intro l hl
  apply selectedFlagChartStep_injective R a
  funext j
  exact (hl.2 j).trans (hstep j).symm

/-- Over a local ring every original full flag belongs to some simultaneous selected chart. -/
theorem selectedFlagChart_exists_local [IsLocalRing A] :
    ∃ (a : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)
      (k : MvPolynomial (FlagChartVariable n) R →ₐ[R] A),
      selectedFlagIncidenceIdeal R a ≤ RingHom.ker k.toRingHom ∧
        ∀ j, selectedFlagChartStep R a k j = F.step j := by
  have hs : ∀ j, ∃ a : Fin (n-j.val) ↪ Fin n,
      Function.Bijective ((F.step j).toSubmodule.mkQ.comp (coordinateInclusion a)) :=
    fun j => grassmannian_exists_bijective_selectedMap_local (F.step j)
  choose a ha using hs
  obtain ⟨k, hk, _⟩ := selectedFlagChart_existsUnique R F a ha
  exact ⟨a, k, hk⟩

end FlagVarieties.Foundations.QuotientCharts
