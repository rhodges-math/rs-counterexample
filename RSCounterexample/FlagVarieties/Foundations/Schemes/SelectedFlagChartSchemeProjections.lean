import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedFlagChartSchemeStructure
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedChartPointMaps

/-!
# Global Grassmannian projections from the glued full-flag scheme

Each local incidence chart retains its original selected quotient at every
step. The regular overlap changes preserve the Grassmannian morphism,
so the local projections glue over the original coefficient base.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] {n : ℕ}
  (a b : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)

theorem selectedFlagOverlapInclusion_step (j : Fin (n+1)) :
    selectedFlagOverlapInclusion R a b ≫ selectedFlagIncidenceChartStepMorphism R a j =
      selectedChartPointMap R (a j)
        ((selectedFlagOverlapPoint R a b).comp (selectedFlagChartVariables R j)) := by
  change Spec.map (CommRingCat.ofHom
    (IsScalarTower.toAlgHom R
      (MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R a)
      (SelectedFlagOverlapRing R a b)).toRingHom) ≫
    (Spec.map (CommRingCat.ofHom
      (((Ideal.Quotient.mkₐ R (selectedFlagIncidenceIdeal R a)).comp
        (selectedFlagChartVariables R j)).toRingHom)) ≫
        selectedChartSchemeChart R n (n-j.val) (a j)) = _
  rw [← Category.assoc, spec_map_algHom_comp]
  rfl

theorem selectedFlagOverlapMap_step (j : Fin (n+1)) :
    selectedFlagOverlapMap R a b ≫ selectedFlagIncidenceChartStepMorphism R b j =
      selectedChartPointMap R (b j)
        (selectedChartTransitionHom R (a j) (b j)
          ((selectedFlagOverlapPoint R a b).comp (selectedFlagChartVariables R j))
          (selectedFlagOverlapPoint_unit R a b j)) := by
  have hq : (selectedFlagOverlapCoordinates R a b).comp
      (Ideal.Quotient.mkₐ R (selectedFlagIncidenceIdeal R b)) =
      selectedFlagChartTransition R a b (selectedFlagOverlapPoint R a b)
        (selectedFlagOverlapPoint_unit R a b) := by
    apply AlgHom.ext
    intro p
    exact selectedFlagOverlapCoordinates_mk R a b p
  change Spec.map (CommRingCat.ofHom (selectedFlagOverlapCoordinates R a b).toRingHom) ≫
    (Spec.map (CommRingCat.ofHom
      (((Ideal.Quotient.mkₐ R (selectedFlagIncidenceIdeal R b)).comp
        (selectedFlagChartVariables R j)).toRingHom)) ≫
        selectedChartSchemeChart R n (n-j.val) (b j)) = _
  rw [← Category.assoc, spec_map_algHom_comp, ← AlgHom.comp_assoc, hq,
    selectedFlagChartTransition_variables]
  rfl

/-- The Grassmannian projection is unchanged across the flag-chart overlap. -/
theorem selectedFlagIncidenceChartStepMorphism_overlap (j : Fin (n+1)) :
    selectedFlagOverlapInclusion R a b ≫ selectedFlagIncidenceChartStepMorphism R a j =
      selectedFlagOverlapMap R a b ≫ selectedFlagIncidenceChartStepMorphism R b j := by
  rw [selectedFlagOverlapInclusion_step, selectedFlagOverlapMap_step]
  exact selectedChartPointMap_transition R (a j) (b j) _ _

variable (n)

/-- The global morphism remembering the j-th quotient of the flag. -/
def selectedFlagChartSchemeStep (j : Fin (n+1)) :
    selectedFlagChartScheme R n ⟶ selectedChartScheme R n (n-j.val) :=
  selectedFlagChartSchemeDesc R n (fun a => selectedFlagIncidenceChartStepMorphism R a j)
    (fun a b => selectedFlagIncidenceChartStepMorphism_overlap R a b j)

@[reassoc]
theorem selectedFlagChartSchemeChart_step
    (a : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n) (j : Fin (n+1)) :
    selectedFlagChartSchemeChart R n a ≫ selectedFlagChartSchemeStep R n j =
      selectedFlagIncidenceChartStepMorphism R a j :=
  selectedFlagChartSchemeChart_desc R n _ _ a

@[reassoc]
theorem selectedFlagChartSchemeStep_toSpec (j : Fin (n+1)) :
    selectedFlagChartSchemeStep R n j ≫ selectedChartSchemeToSpec R n (n-j.val) =
      selectedFlagChartSchemeToSpec R n := by
  apply selectedFlagChartScheme_hom_ext R n
  intro a
  rw [← Category.assoc, selectedFlagChartSchemeChart_step,
    selectedFlagIncidenceChartStepMorphism_toSpec, selectedFlagChartSchemeChart_toSpec]

end FlagVarieties.Foundations.QuotientCharts
