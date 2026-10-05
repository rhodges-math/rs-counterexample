import Schubert.FlagVarieties.Foundations.Schemes.GlobalQuotientFlagAffine

/-!
# Gluing classifying maps of quotient-sheaf flags

The local maps agree on full scheme-theoretic intersections because their
universal flags recover the same original quotient maps there. Compatibility
is derived, including for nonaffine and nonseparated intersections.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u v
variable (R : Type u) [CommRing R] {X : Scheme.{u}} {n : ℕ}
  (b : X ⟶ Spec (CommRingCat.of R)) (F : QuotientFlagFamily X n)
  (C : X.OpenCover.{v}) (f : ∀ i, C.X i ⟶ selectedFlagChartScheme R n)
  (hf : ∀ i, f i ≫ selectedFlagChartSchemeToSpec R n = C.f i ≫ b)
  (e : ∀ i j, (Scheme.Modules.pullback (f i)).obj (selectedFlagUniversalTarget R n j) ≅
    (Scheme.Modules.pullback (C.f i)).obj (F.target j))
  (he : ∀ i j, coordinatePullbackQuotient (f i) (selectedFlagUniversalQuotient R n j) ≫
    (e i j).hom = coordinatePullbackQuotient (C.f i) (F.quotient j))

include hf he

theorem quotientFlagMorphism_overlap (i j : C.I₀) :
    pullback.fst (C.f i) (C.f j) ≫ f i = pullback.snd (C.f i) (C.f j) ≫ f j := by
  let l := pullback.fst (C.f i) (C.f j)
  let r := pullback.snd (C.f i) (C.f j)
  let el := fun k => coordinateQuotientComparisonPullback l (f i) (e i k) ≪≫
    (Scheme.Modules.pullbackComp l (C.f i)).app (F.target k)
  let er := fun k => coordinateQuotientComparisonPullback r (f j) (e j k) ≪≫
    (Scheme.Modules.pullbackComp r (C.f j)).app (F.target k)
  have hl (k : Fin (n+1)) :
      coordinatePullbackQuotient (l ≫ f i) (selectedFlagUniversalQuotient R n k) ≫
        (el k).hom = coordinatePullbackQuotient (l ≫ C.f i) (F.quotient k) := by
    simp only [el, Iso.trans_hom, Iso.app_hom]
    rw [← Category.assoc, coordinateQuotientComparisonPullback_source l (f i) _ _ (e i k) (he i k),
      coordinatePullbackQuotient_comp_hom]
  have hr (k : Fin (n+1)) :
      coordinatePullbackQuotient (r ≫ f j) (selectedFlagUniversalQuotient R n k) ≫
        (er k).hom = coordinatePullbackQuotient (r ≫ C.f j) (F.quotient k) := by
    simp only [er, Iso.trans_hom, Iso.app_hom]
    rw [← Category.assoc, coordinateQuotientComparisonPullback_source r (f j) _ _ (e j k) (he j k),
      coordinatePullbackQuotient_comp_hom]
  have hcomp : l ≫ C.f i = r ≫ C.f j := pullback.condition
  apply selectedFlagUniversalMorphism_unique R (l ≫ f i) (r ≫ f j)
      (by simp only [Category.assoc, hf]; exact congrArg (fun g => g ≫ b) hcomp)
      (fun k => el k ≪≫ (Scheme.Modules.pullbackCongr hcomp).app (F.target k) ≪≫ (er k).symm)
  intro k
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Category.assoc, hl k]
  change (coordinatePullbackQuotient (l ≫ C.f i) (F.quotient k) ≫
    (Scheme.Modules.pullbackCongr hcomp).hom.app (F.target k)) ≫ (er k).inv = _
  rw [coordinatePullbackQuotient_congr, ← hr k]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The morphism `X ⟶ Flₙ` glued from local classifying morphisms on an open cover of `X`. -/
def quotientFlagMorphismGlue : X ⟶ selectedFlagChartScheme R n :=
  C.glueMorphisms f (quotientFlagMorphism_overlap R b F C f hf e he)

@[reassoc]
theorem quotientFlagMorphismGlue_local (i : C.I₀) :
    C.f i ≫ quotientFlagMorphismGlue R b F C f hf e he = f i :=
  C.ι_glueMorphisms f _ i

@[reassoc]
theorem quotientFlagMorphismGlue_toSpec :
    quotientFlagMorphismGlue R b F C f hf e he ≫ selectedFlagChartSchemeToSpec R n = b := by
  apply C.hom_ext
  intro i
  rw [← Category.assoc, quotientFlagMorphismGlue_local, hf]

end FlagVarieties.Foundations.QuotientCharts
