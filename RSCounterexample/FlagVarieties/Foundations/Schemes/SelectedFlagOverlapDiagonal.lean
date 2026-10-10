import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedFlagOverlapScheme

/-! # Diagonal and inverse identities for full-flag scheme overlaps -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] {n : ℕ}
  (a b : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)

theorem selectedFlagOverlapDeterminant_diagonal_unit :
    IsUnit (selectedFlagOverlapDeterminant R a a) := by
  have h : IsUnit (selectedFlagOverlapPolynomial R a a) := by
    apply IsUnit.prod_univ_iff.mpr
    intro j
    exact (selectedPolynomialBlock_diagonal_unit R (a j)).map (selectedFlagChartVariables R j)
  exact h.map (Ideal.Quotient.mk (selectedFlagIncidenceIdeal R a))

instance selectedFlagOverlapInclusion_diagonal_iso :
    IsIso (selectedFlagOverlapInclusion R a a) := by
  let e := IsLocalization.atUnit
    (MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R a)
    (SelectedFlagOverlapRing R a a) (selectedFlagOverlapDeterminant R a a)
    (selectedFlagOverlapDeterminant_diagonal_unit R a)
  have he : e.toRingEquiv.toCommRingCatIso.hom = CommRingCat.ofHom
      (algebraMap (MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R a)
        (SelectedFlagOverlapRing R a a)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    exact e.toAlgHom.commutes p
  unfold selectedFlagOverlapInclusion
  rw [← he]
  infer_instance

theorem selectedFlagChartTransition_self {A : Type u} [CommRing A] [Algebra R A]
    (k : MvPolynomial (FlagChartVariable n) R →ₐ[R] A)
    (h : ∀ j, IsUnit ((k.comp (selectedFlagChartVariables R j))
      (selectedPolynomialBlock R (a j) (a j)).det)) :
    selectedFlagChartTransition R a a k h = k := by
  apply selectedFlagChartEvaluation_ext R
  intro j
  rw [selectedFlagChartTransition_variables]
  exact selectedChartTransitionHom_self R (a j) _ _

theorem selectedFlagOverlapCoordinates_diagonal :
    selectedFlagOverlapCoordinates R a a = IsScalarTower.toAlgHom R
      (MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R a)
      (SelectedFlagOverlapRing R a a) := by
  apply AlgHom.ext
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [selectedFlagOverlapCoordinates_mk, selectedFlagChartTransition_self]
  rfl

theorem selectedFlagOverlapSchemeIso_self : (selectedFlagOverlapSchemeIso R a a).hom = 𝟙 _ := by
  have h : selectedFlagOverlapLift R a a = AlgHom.id R (SelectedFlagOverlapRing R a a) := by
    apply AlgHom.toRingHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers (selectedFlagOverlapDeterminant R a a))
    apply RingHom.ext
    intro p
    change selectedFlagOverlapLift R a a
      (algebraMap _ (SelectedFlagOverlapRing R a a) p) =
        algebraMap _ (SelectedFlagOverlapRing R a a) p
    rw [selectedFlagOverlapLift_algebraMap]
    exact AlgHom.congr_fun (selectedFlagOverlapCoordinates_diagonal R a) p
  change Spec.map (CommRingCat.ofHom (selectedFlagOverlapLift R a a).toRingHom) = _
  rw [h]
  exact Scheme.Spec.map_id _

theorem selectedFlagOverlapSchemeIso_reverse :
    (selectedFlagOverlapSchemeIso R a b).hom ≫ (selectedFlagOverlapSchemeIso R b a).hom = 𝟙 _ := by
  change Spec.map (CommRingCat.ofHom (selectedFlagOverlapLift R a b).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (selectedFlagOverlapLift R b a).toRingHom) = _
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((selectedFlagOverlapLift R a b).comp (selectedFlagOverlapLift R b a)).toRingHom) = _
  rw [selectedFlagOverlapLift_comp]
  exact Scheme.Spec.map_id _

end FlagVarieties.Foundations.QuotientCharts
