import RSCounterexample.FlagVarieties.Foundations.Schemes.GlobalQuotientFlagGluing
import RSCounterexample.FlagVarieties.Foundations.Schemes.GlobalQuotientFlagDescent

/-!
# Universal classification of flags over arbitrary schemes

Every quotient-sheaf flag of the original labelled free sheaf has a unique
classifying morphism. Its universal pullback recovers all original quotient
maps and adjacent arrows. All local maps, overlap equations and comparisons
are derived from the given flag; neither affineness nor separation is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] {X : Scheme.{u}} {n : ℕ}
  (b : X ⟶ Spec (CommRingCat.of R)) (F : QuotientFlagFamily X n)

/-- The morphism `X ⟶ Flₙ` classifying a family `F` of quotient flags on `X`, glued from the
classifying morphisms on the affine open cover of `X`. -/
def globalQuotientFlagMorphism : X ⟶ selectedFlagChartScheme R n :=
  quotientFlagMorphismGlue R b F X.affineOpenCover.openCover
    (fun i => quotientFlagAffineMorphism R b F _ (X.affineOpenCover.f i))
    (fun i => quotientFlagAffineMorphism_toSpec R b F _ (X.affineOpenCover.f i))
    (fun i => quotientFlagAffineIso R b F _ (X.affineOpenCover.f i))
    (fun i => quotientFlagAffineIso_source R b F _ (X.affineOpenCover.f i))

@[reassoc]
theorem globalQuotientFlagMorphism_local (i : X.affineOpenCover.I₀) :
    X.affineOpenCover.f i ≫ globalQuotientFlagMorphism R b F =
      quotientFlagAffineMorphism R b F _ (X.affineOpenCover.f i) :=
  quotientFlagMorphismGlue_local R b F _ _ _ _ _ i

@[reassoc]
theorem globalQuotientFlagMorphism_toSpec :
    globalQuotientFlagMorphism R b F ≫ selectedFlagChartSchemeToSpec R n = b :=
  quotientFlagMorphismGlue_toSpec R b F _ _ _ _ _

/-- The pullback of the universal step-`j` quotient along `globalQuotientFlagMorphism` is the
step-`j` quotient of `F`. -/
def globalQuotientFlagUniversalIso (j : Fin (n+1)) :
    (Scheme.Modules.pullback (globalQuotientFlagMorphism R b F)).obj
      (selectedFlagUniversalTarget R n j) ≅ F.target j :=
  selectedFlagUniversalIsoOfLocal R F X.affineOpenCover.openCover
    (fun i => quotientFlagAffineMorphism R b F _ (X.affineOpenCover.f i))
    (fun i => quotientFlagAffineIso R b F _ (X.affineOpenCover.f i))
    (fun i => quotientFlagAffineIso_source R b F _ (X.affineOpenCover.f i))
    (globalQuotientFlagMorphism R b F) (globalQuotientFlagMorphism_local R b F) j

@[reassoc]
theorem globalQuotientFlagUniversalIso_source (j : Fin (n+1)) :
    coordinatePullbackQuotient (globalQuotientFlagMorphism R b F)
        (selectedFlagUniversalQuotient R n j) ≫
      (globalQuotientFlagUniversalIso R b F j).hom = F.quotient j :=
  selectedFlagUniversalIsoOfLocal_source R F X.affineOpenCover.openCover
    (fun i => quotientFlagAffineMorphism R b F _ (X.affineOpenCover.f i))
    (fun i => quotientFlagAffineIso R b F _ (X.affineOpenCover.f i))
    (fun i => quotientFlagAffineIso_source R b F _ (X.affineOpenCover.f i))
    (globalQuotientFlagMorphism R b F) (globalQuotientFlagMorphism_local R b F) j

@[reassoc]
theorem globalQuotientFlagUniversalIso_transition (j : Fin n) :
    (Scheme.Modules.pullback (globalQuotientFlagMorphism R b F)).map
        (selectedFlagUniversalTransition R n j) ≫
      (globalQuotientFlagUniversalIso R b F j.succ).hom =
    (globalQuotientFlagUniversalIso R b F j.castSucc).hom ≫ F.transition j :=
  QuotientFlagFamily.transition_natural_of_source
    ((selectedFlagUniversalFamily R n).pullback (globalQuotientFlagMorphism R b F)) F
    (fun j => (globalQuotientFlagUniversalIso R b F j).hom)
    (globalQuotientFlagUniversalIso_source R b F) j

theorem globalQuotientFlagMorphism_unique
    (f : X ⟶ selectedFlagChartScheme R n)
    (hf : f ≫ selectedFlagChartSchemeToSpec R n = b)
    (e : ∀ j, (Scheme.Modules.pullback f).obj (selectedFlagUniversalTarget R n j) ≅ F.target j)
    (he : ∀ j, coordinatePullbackQuotient f (selectedFlagUniversalQuotient R n j) ≫
      (e j).hom = F.quotient j) : f = globalQuotientFlagMorphism R b F := by
  apply selectedFlagUniversalMorphism_unique R f (globalQuotientFlagMorphism R b F)
      (hf.trans (globalQuotientFlagMorphism_toSpec R b F).symm)
      (fun j => e j ≪≫ (globalQuotientFlagUniversalIso R b F j).symm)
  intro j
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, he j, ← globalQuotientFlagUniversalIso_source R b F j]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Full universal property for flags over arbitrary scheme bases. -/
theorem globalQuotientFlagUniversal_existsUnique :
    ∃! f : {f : X ⟶ selectedFlagChartScheme R n //
      f ≫ selectedFlagChartSchemeToSpec R n = b},
      ∃ e : ∀ j, (Scheme.Modules.pullback f.val).obj (selectedFlagUniversalTarget R n j) ≅
          F.target j,
        ∀ j, coordinatePullbackQuotient f.val (selectedFlagUniversalQuotient R n j) ≫
          (e j).hom = F.quotient j := by
  refine ⟨⟨globalQuotientFlagMorphism R b F, globalQuotientFlagMorphism_toSpec R b F⟩,
    ⟨globalQuotientFlagUniversalIso R b F, globalQuotientFlagUniversalIso_source R b F⟩, ?_⟩
  rintro f ⟨e, he⟩
  exact Subtype.ext (globalQuotientFlagMorphism_unique R b F f.val f.property e he)

end FlagVarieties.Foundations.QuotientCharts
