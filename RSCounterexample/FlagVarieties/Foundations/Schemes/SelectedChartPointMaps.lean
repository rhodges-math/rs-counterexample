import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedChartSchemeStructure

/-!+# Compatible maps from affine quotient presentations

Two normalized coordinate presentations of the same quotient determine
the same scheme morphism into the glued chart scheme. This is an equality of
scheme morphisms over arbitrary commutative base algebras, not only field points.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory

universe u

variable (R : Type u) [CommRing R]

theorem spec_map_algHom_comp
    {P S A : Type u} [CommRing P] [CommRing S] [CommRing A]
    [Algebra R P] [Algebra R S] [Algebra R A]
    (g : S →ₐ[R] A) (f : P →ₐ[R] S) :
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ Spec.map (CommRingCat.ofHom f.toRingHom) =
      Spec.map (CommRingCat.ofHom (g.comp f).toRingHom) :=
  (Spec.map_comp _ _).symm

variable {n d : ℕ} (a b : Fin d ↪ Fin n)
  {A : Type u} [CommRing A] [Algebra R A]

/-- The morphism associated with a normalized affine quotient presentation. -/
def selectedChartPointMap (f : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A) :
    Spec (CommRingCat.of A) ⟶ selectedChartScheme R n d :=
  Spec.map (CommRingCat.ofHom f.toRingHom) ≫ selectedChartSchemeChart R n d a

/-- The two chart maps agree on the specified determinant overlap. -/
theorem selectedChartSchemeChart_overlap :
    selectedChartOverlapMap R a b ≫ selectedChartSchemeChart R n d b =
      selectedChartOverlapInclusion R a b ≫ selectedChartSchemeChart R n d a := by
  have h := (selectedChartGlueData R n d).glue_condition (ULift.up a) (ULift.up b)
  change (selectedChartOverlapIso R a b).hom ≫ selectedChartOverlapInclusion R b a ≫
    selectedChartSchemeChart R n d b =
      selectedChartOverlapInclusion R a b ≫ selectedChartSchemeChart R n d a at h
  rw [← Category.assoc, selectedChartOverlapIso_hom_inclusion] at h
  exact h

/-- Regular change of selected coordinates leaves the affine scheme map unchanged. -/
theorem selectedChartPointMap_transition
    (f : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A)
    (h : IsUnit (f (selectedPolynomialBlock R a b).det)) :
    selectedChartPointMap R a f =
      selectedChartPointMap R b (selectedChartTransitionHom R a b f h) := by
  let g : Localization.Away (selectedPolynomialBlock R a b).det →ₐ[R] A :=
    IsLocalization.Away.liftAlgHom (selectedPolynomialBlock R a b).det h
  have hg : g.comp (IsScalarTower.toAlgHom R (MvPolynomial (Fin d × Fin (n - d)) R)
      (Localization.Away (selectedPolynomialBlock R a b).det)) = f := by
    ext p
    simp [g]
  have hfirst : Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      selectedChartOverlapInclusion R a b = Spec.map (CommRingCat.ofHom f.toRingHom) := by
    exact (spec_map_algHom_comp R g
      (IsScalarTower.toAlgHom R (MvPolynomial (Fin d × Fin (n - d)) R)
        (Localization.Away (selectedPolynomialBlock R a b).det))).trans
      (congrArg (fun q : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A =>
        Spec.map (CommRingCat.ofHom q.toRingHom)) hg)
  have hsecond : Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      selectedChartOverlapMap R a b =
        Spec.map (CommRingCat.ofHom (selectedChartTransitionHom R a b f h).toRingHom) :=
    spec_map_algHom_comp R g
      (matrixOverlapCoordinates R (selectedPolynomialBlock R a b) (remainingPolynomialBlock R a b))
  unfold selectedChartPointMap
  rw [← hfirst, Category.assoc, ← selectedChartSchemeChart_overlap,
    ← Category.assoc, hsecond]

/-- Equality of quotient modules implies equality of the resulting scheme maps. -/
theorem selectedChartPointMap_eq_of_quotient_eq
    (f g : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A)
    (h : selectedChartPoint R a f = selectedChartPoint R b g) :
    selectedChartPointMap R a f = selectedChartPointMap R b g := by
  have hb : Function.Bijective ((selectedChartPoint R a f).toSubmodule.mkQ.comp
      (coordinateInclusion b)) := by
    rw [h]
    exact selectedChartPoint_selected_bijective R b g
  have hu := (selectedPolynomialBlock_open_iff R a b f _
    (selectedChartPoint_presented R a f)).mpr hb
  have he : selectedChartTransitionHom R a b f hu = g := by
    apply (matrixEvaluationEquiv R d (n - d) A).injective
    apply matrixGrassmannianChartEquiv.injective
    apply Subtype.ext
    have ht := selectedChartTransitionHom_represents R a b f hu _
      (selectedChartPoint_presented R a f)
    rw [h] at ht
    exact ht.trans (selectedChartPoint_presented R b g).symm
  exact (selectedChartPointMap_transition R a b f hu).trans
    (congrArg (selectedChartPointMap R b) he)

end FlagVarieties.Foundations.QuotientCharts
