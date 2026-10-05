import Schubert.FlagVarieties.Foundations.Schemes.GlobalLocallyFreeQuotientAffine
import Schubert.FlagVarieties.Foundations.Schemes.GlobalLocallyFreeQuotientGluing

/-!
# Classifying locally free quotients on arbitrary schemes

An epimorphism from the labelled rank-n free sheaf to a locally
free rank-d sheaf determines a unique morphism to the constructed
Grassmannian scheme. Its universal pullback is isomorphic to the given
quotient, preserving the original source map. All local maps, overlap
equalities, and sheaf comparisons are derived.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] {X : Scheme.{u}} {n : ℕ} {M : X.Modules}
  (b : X ⟶ Spec (CommRingCat.of R))
  (q : coordinateFreeSheaf X n ⟶ M) [Epi q] (d : ℕ)
  (hfree : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty (M.over U ≅
      SheafOfModules.free (R := X.ringCatSheaf.over U) (CoordinateIndex.{u} d)))

/-- The classifying morphism on an arbitrary base scheme. -/
def globalLocallyFreeQuotientMorphism : X ⟶ selectedChartScheme R n d :=
  locallyFreeQuotientMorphismGlue R b q X.affineOpenCover.openCover
    (fun i => locallyFreeQuotientAffineMorphism R b q d hfree _ (X.affineOpenCover.f i))
    (fun i => locallyFreeQuotientAffineMorphism_toSpec R b q d hfree _ (X.affineOpenCover.f i))
    (fun i => locallyFreeQuotientAffineIso R b q d hfree _ (X.affineOpenCover.f i))
    (fun i => locallyFreeQuotientAffineIso_source R b q d hfree _ (X.affineOpenCover.f i))

@[reassoc]
theorem globalLocallyFreeQuotientMorphism_toSpec :
    globalLocallyFreeQuotientMorphism R b q d hfree ≫
      selectedChartSchemeToSpec R n d = b :=
  locallyFreeQuotientMorphismGlue_toSpec R b q _ _ _ _ _

/-- The universal pullback recovers the given sheaf on the whole base. -/
def globalLocallyFreeUniversalIso :
    (Scheme.Modules.pullback (globalLocallyFreeQuotientMorphism R b q d hfree)).obj
      (selectedUniversalQuotientSheaf R n d) ≅ M :=
  locallyFreeQuotientMorphismGlueIso R b q X.affineOpenCover.openCover
    (fun i => locallyFreeQuotientAffineMorphism R b q d hfree _ (X.affineOpenCover.f i))
    (fun i => locallyFreeQuotientAffineMorphism_toSpec R b q d hfree _ (X.affineOpenCover.f i))
    (fun i => locallyFreeQuotientAffineIso R b q d hfree _ (X.affineOpenCover.f i))
    (fun i => locallyFreeQuotientAffineIso_source R b q d hfree _ (X.affineOpenCover.f i))

@[reassoc]
theorem globalLocallyFreeUniversalIso_source :
    coordinatePullbackQuotient (globalLocallyFreeQuotientMorphism R b q d hfree)
        (selectedUniversalQuotient R n d) ≫
      (globalLocallyFreeUniversalIso R b q d hfree).hom = q :=
  locallyFreeQuotientMorphismGlueIso_source R b q _ _ _ _ _

/-- Source-preserving universal recovery determines the classifying map uniquely. -/
theorem globalLocallyFreeQuotientMorphism_unique
    (F : X ⟶ selectedChartScheme R n d)
    (hF : F ≫ selectedChartSchemeToSpec R n d = b)
    (e : (Scheme.Modules.pullback F).obj (selectedUniversalQuotientSheaf R n d) ≅ M)
    (he : coordinatePullbackQuotient F (selectedUniversalQuotient R n d) ≫ e.hom = q) :
    F = globalLocallyFreeQuotientMorphism R b q d hfree := by
  apply selectedUniversalMorphism_unique R F (globalLocallyFreeQuotientMorphism R b q d hfree)
    (hF.trans (globalLocallyFreeQuotientMorphism_toSpec R b q d hfree).symm)
    (e ≪≫ (globalLocallyFreeUniversalIso R b q d hfree).symm)
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, he]
  apply (cancel_mono (globalLocallyFreeUniversalIso R b q d hfree).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (globalLocallyFreeUniversalIso_source R b q d hfree).symm

include hfree

/-- Full universal property on arbitrary scheme bases, with the original quotient map. -/
theorem globalLocallyFreeUniversal_existsUnique :
    ∃! F : {F : X ⟶ selectedChartScheme R n d //
      F ≫ selectedChartSchemeToSpec R n d = b},
      ∃ e : (Scheme.Modules.pullback F.val).obj (selectedUniversalQuotientSheaf R n d) ≅ M,
        coordinatePullbackQuotient F.val (selectedUniversalQuotient R n d) ≫ e.hom = q := by
  refine ⟨⟨globalLocallyFreeQuotientMorphism R b q d hfree,
    globalLocallyFreeQuotientMorphism_toSpec R b q d hfree⟩,
    ⟨globalLocallyFreeUniversalIso R b q d hfree,
      globalLocallyFreeUniversalIso_source R b q d hfree⟩, ?_⟩
  rintro F ⟨e, he⟩
  exact Subtype.ext (globalLocallyFreeQuotientMorphism_unique R b q d hfree F.val F.property e he)

end FlagVarieties.Foundations.QuotientCharts
