import Schubert.FlagVarieties.Foundations.Schemes.GlobalLocallyFreeQuotientDescent
import Schubert.FlagVarieties.Foundations.Schemes.CoordinateQuotientPullbackComparison
import Schubert.FlagVarieties.Foundations.Schemes.SelectedUniversalMorphismUniqueness

/-!
# Gluing local classifying morphisms of a quotient

The overlap equality of scheme morphisms is proved from their
universal quotients. It is not a compatibility hypothesis on the local
maps. No affineness or separation condition is imposed on intersections.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u v
variable (R : Type u) [CommRing R] {X : Scheme.{u}} {n d : ℕ} {M : X.Modules}
  (b : X ⟶ Spec (CommRingCat.of R))
  (q : coordinateFreeSheaf X n ⟶ M) [Epi q] (C : X.OpenCover.{v})
  (f : ∀ i, C.X i ⟶ selectedChartScheme R n d)
  (hf : ∀ i, f i ≫ selectedChartSchemeToSpec R n d = C.f i ≫ b)
  (e : ∀ i, (Scheme.Modules.pullback (f i)).obj (selectedUniversalQuotientSheaf R n d) ≅
    (Scheme.Modules.pullback (C.f i)).obj M)
  (he : ∀ i, coordinatePullbackQuotient (f i) (selectedUniversalQuotient R n d) ≫
    (e i).hom = coordinatePullbackQuotient (C.f i) q)

include hf he

omit [Epi q] in
/-- Local classifying maps agree on full scheme-theoretic intersections. -/
theorem locallyFreeQuotientMorphism_overlap (i j : C.I₀) :
    pullback.fst (C.f i) (C.f j) ≫ f i = pullback.snd (C.f i) (C.f j) ≫ f j := by
  let l := pullback.fst (C.f i) (C.f j)
  let r := pullback.snd (C.f i) (C.f j)
  let el := coordinateQuotientComparisonPullback l (f i) (e i) ≪≫
    (Scheme.Modules.pullbackComp l (C.f i)).app M
  let er := coordinateQuotientComparisonPullback r (f j) (e j) ≪≫
    (Scheme.Modules.pullbackComp r (C.f j)).app M
  have hl : coordinatePullbackQuotient (l ≫ f i) (selectedUniversalQuotient R n d) ≫
      el.hom = coordinatePullbackQuotient (l ≫ C.f i) q := by
    simp only [el, Iso.trans_hom, Iso.app_hom]
    rw [← Category.assoc, coordinateQuotientComparisonPullback_source l (f i) _ _ (e i) (he i),
      coordinatePullbackQuotient_comp_hom]
  have hr : coordinatePullbackQuotient (r ≫ f j) (selectedUniversalQuotient R n d) ≫
      er.hom = coordinatePullbackQuotient (r ≫ C.f j) q := by
    simp only [er, Iso.trans_hom, Iso.app_hom]
    rw [← Category.assoc, coordinateQuotientComparisonPullback_source r (f j) _ _ (e j) (he j),
      coordinatePullbackQuotient_comp_hom]
  have hcomp : l ≫ C.f i = r ≫ C.f j := pullback.condition
  let c := (Scheme.Modules.pullbackCongr hcomp).app M
  apply selectedUniversalMorphism_unique R (l ≫ f i) (r ≫ f j)
      (by simp only [Category.assoc, hf]; exact congrArg (fun g => g ≫ b) hcomp)
      (el ≪≫ c ≪≫ er.symm)
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Category.assoc, hl]
  change (coordinatePullbackQuotient (l ≫ C.f i) q ≫
    (Scheme.Modules.pullbackCongr hcomp).hom.app M) ≫ er.inv = _
  rw [coordinatePullbackQuotient_congr, ← hr]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Scheme gluing of the local classifying morphisms. -/
def locallyFreeQuotientMorphismGlue : X ⟶ selectedChartScheme R n d :=
  C.glueMorphisms f (locallyFreeQuotientMorphism_overlap R b q C f hf e he)

omit [Epi q] in
@[reassoc]
theorem locallyFreeQuotientMorphismGlue_local (i : C.I₀) :
    C.f i ≫ locallyFreeQuotientMorphismGlue R b q C f hf e he = f i :=
  C.ι_glueMorphisms f _ i

omit [Epi q] in
@[reassoc]
theorem locallyFreeQuotientMorphismGlue_toSpec :
    locallyFreeQuotientMorphismGlue R b q C f hf e he ≫
      selectedChartSchemeToSpec R n d = b := by
  apply C.hom_ext
  intro i
  rw [← Category.assoc, locallyFreeQuotientMorphismGlue_local, hf]

/-- The glued classifying morphism recovers the given global quotient. -/
def locallyFreeQuotientMorphismGlueIso :
    (Scheme.Modules.pullback (locallyFreeQuotientMorphismGlue R b q C f hf e he)).obj
      (selectedUniversalQuotientSheaf R n d) ≅ M :=
  selectedUniversalQuotientIsoOfLocal R q C f e he _
    (locallyFreeQuotientMorphismGlue_local R b q C f hf e he)

@[reassoc]
theorem locallyFreeQuotientMorphismGlueIso_source :
    coordinatePullbackQuotient (locallyFreeQuotientMorphismGlue R b q C f hf e he)
        (selectedUniversalQuotient R n d) ≫
      (locallyFreeQuotientMorphismGlueIso R b q C f hf e he).hom = q :=
  selectedUniversalQuotientIsoOfLocal_source R q C f e he _ _

end FlagVarieties.Foundations.QuotientCharts
