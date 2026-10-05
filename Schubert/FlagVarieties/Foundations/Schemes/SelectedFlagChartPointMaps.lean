import Schubert.FlagVarieties.Foundations.Schemes.SelectedFlagChartSchemeProjections
import Schubert.FlagVarieties.Foundations.Flags.SelectedFlagOverlapEvaluationTransition

/-! # Affine scheme maps from joint flag-chart parameters -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] {n : ℕ}
  (a b : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)
  {A : Type u} [CommRing A] [Algebra R A]

/-- The `A`-point of the flag scheme in the chart `a` with chart coordinates `k`. -/
def selectedFlagChartPointMap (k : MvPolynomial (FlagChartVariable n) R →ₐ[R] A)
    (hk : selectedFlagIncidenceIdeal R a ≤ RingHom.ker k.toRingHom) :
    Spec (CommRingCat.of A) ⟶ selectedFlagChartScheme R n :=
  Spec.map (CommRingCat.ofHom (selectedFlagIncidenceEvaluation R a k hk).toRingHom) ≫
    selectedFlagChartSchemeChart R n a

@[reassoc]
theorem selectedFlagChartPointMap_step (k : MvPolynomial (FlagChartVariable n) R →ₐ[R] A)
    (hk : selectedFlagIncidenceIdeal R a ≤ RingHom.ker k.toRingHom) (j : Fin (n+1)) :
    selectedFlagChartPointMap R a k hk ≫ selectedFlagChartSchemeStep R n j =
      selectedChartPointMap R (a j) (k.comp (selectedFlagChartVariables R j)) := by
  have he : (selectedFlagIncidenceEvaluation R a k hk).comp
      ((Ideal.Quotient.mkₐ R (selectedFlagIncidenceIdeal R a)).comp
        (selectedFlagChartVariables R j)) = k.comp (selectedFlagChartVariables R j) := by
    apply AlgHom.ext
    intro p
    rfl
  rw [selectedFlagChartPointMap, Category.assoc, selectedFlagChartSchemeChart_step]
  change Spec.map (CommRingCat.ofHom (selectedFlagIncidenceEvaluation R a k hk).toRingHom) ≫
    (Spec.map (CommRingCat.ofHom
      (((Ideal.Quotient.mkₐ R (selectedFlagIncidenceIdeal R a)).comp
        (selectedFlagChartVariables R j)).toRingHom)) ≫
      selectedChartSchemeChart R n (n-j.val) (a j)) = _
  rw [← Category.assoc, spec_map_algHom_comp, he]
  rfl

theorem selectedFlagChartSchemeChart_overlap :
    selectedFlagOverlapMap R a b ≫ selectedFlagChartSchemeChart R n b =
      selectedFlagOverlapInclusion R a b ≫ selectedFlagChartSchemeChart R n a := by
  have h := (selectedFlagChartGlueData R n).glue_condition (ULift.up a) (ULift.up b)
  change (selectedFlagOverlapSchemeIso R a b).hom ≫ selectedFlagOverlapInclusion R b a ≫
    selectedFlagChartSchemeChart R n b =
      selectedFlagOverlapInclusion R a b ≫ selectedFlagChartSchemeChart R n a at h
  rw [← Category.assoc, selectedFlagOverlapSchemeIso_hom_inclusion] at h
  exact h

set_option maxHeartbeats 800000 in
theorem selectedFlagChartPointMap_transition
    (k : MvPolynomial (FlagChartVariable n) R →ₐ[R] A)
    (hk : selectedFlagIncidenceIdeal R a ≤ RingHom.ker k.toRingHom)
    (h : ∀ j, IsUnit ((k.comp (selectedFlagChartVariables R j))
      (selectedPolynomialBlock R (a j) (b j)).det)) :
    selectedFlagChartPointMap R a k hk =
      selectedFlagChartPointMap R b (selectedFlagChartTransition R a b k h)
        (selectedFlagChartTransition_ideal R a b k h hk) := by
  let g : SelectedFlagOverlapRing R a b →ₐ[R] A :=
    selectedFlagOverlapEvaluation R a b k hk h
  have hfirst : Spec.map (CommRingCat.ofHom g.toRingHom) ≫ selectedFlagOverlapInclusion R a b =
      Spec.map (CommRingCat.ofHom (selectedFlagIncidenceEvaluation R a k hk).toRingHom) := by
    have hg : g.comp (IsScalarTower.toAlgHom R
        (MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R a)
        (SelectedFlagOverlapRing R a b)) = selectedFlagIncidenceEvaluation R a k hk := by
      apply AlgHom.ext
      intro p
      exact selectedFlagOverlapEvaluation_algebraMap R a b k hk h p
    exact (spec_map_algHom_comp R g
      (IsScalarTower.toAlgHom R
        (MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R a)
        (SelectedFlagOverlapRing R a b))).trans
      (congrArg (fun q :
        (MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R a) →ₐ[R] A =>
          Spec.map (CommRingCat.ofHom q.toRingHom)) hg)
  have hsecond : Spec.map (CommRingCat.ofHom g.toRingHom) ≫ selectedFlagOverlapMap R a b =
      Spec.map (CommRingCat.ofHom
        (selectedFlagIncidenceEvaluation R b (selectedFlagChartTransition R a b k h)
          (selectedFlagChartTransition_ideal R a b k h hk)).toRingHom) := by
    have he := selectedFlagOverlapEvaluation_coordinates R a b k hk h
    change g.comp (selectedFlagOverlapCoordinates R a b) = _ at he
    change Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (selectedFlagOverlapCoordinates R a b).toRingHom) = _
    rw [spec_map_algHom_comp, he]
  unfold selectedFlagChartPointMap
  calc
    _ = (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ selectedFlagOverlapInclusion R a b) ≫
        selectedFlagChartSchemeChart R n a :=
      congrArg (fun q => q ≫ selectedFlagChartSchemeChart R n a) hfirst.symm
    _ = Spec.map (CommRingCat.ofHom g.toRingHom) ≫
        (selectedFlagOverlapInclusion R a b ≫ selectedFlagChartSchemeChart R n a) :=
      Category.assoc _ _ _
    _ = Spec.map (CommRingCat.ofHom g.toRingHom) ≫
        (selectedFlagOverlapMap R a b ≫ selectedFlagChartSchemeChart R n b) :=
      congrArg (fun q => Spec.map (CommRingCat.ofHom g.toRingHom) ≫ q)
        (selectedFlagChartSchemeChart_overlap R a b).symm
    _ = (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ selectedFlagOverlapMap R a b) ≫
        selectedFlagChartSchemeChart R n b := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun q => q ≫ selectedFlagChartSchemeChart R n b) hsecond

end FlagVarieties.Foundations.QuotientCharts
