import RSCounterexample.FlagVarieties.Foundations.Schemes.SimultaneousFlagCoordinateRelativeMorphism
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedFlagAffineUniversalRecovery
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedFlagUniversalFamily
import RSCounterexample.FlagVarieties.Foundations.Schemes.QuotientFlagFamilyPullback
import RSCounterexample.FlagVarieties.Foundations.Schemes.QuotientFlagFamilyComparison

/-!
# Affine universal classification of quotient-sheaf flags

An arbitrary affine flag supplies its own original coordinate kernels and
simultaneous principal presentations. Their derived classifying map recovers
each original quotient and all adjacent arrows. No chosen basis, chart
compatibility, or existence of a classifying map is an input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] (A : CommRingCat.{u}) [Algebra R A]
  {n : ℕ} (F : QuotientFlagFamily (Spec A) n)

/-- The morphism `Spec A ⟶ Flₙ` classifying the family `F` of quotient flags on `Spec A`. -/
def affineQuotientFlagMorphism : Spec A ⟶ selectedFlagChartScheme R n :=
  simultaneousFlagRelativeMorphism R (F.toRingFlag A)

@[reassoc]
theorem affineQuotientFlagMorphism_toSpec :
    affineQuotientFlagMorphism R A F ≫ selectedFlagChartSchemeToSpec R n =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) :=
  simultaneousFlagRelativeMorphism_toSpec R (F.toRingFlag A)

@[reassoc]
theorem affineQuotientFlagMorphism_step (j : Fin (n+1)) :
    affineQuotientFlagMorphism R A F ≫ selectedFlagChartSchemeStep R n j =
      selectedQuotientMorphism R ((F.toRingFlag A).step j) :=
  simultaneousFlagRelativeMorphism_step R (F.toRingFlag A) j

/-- The pullback of the universal step-`j` quotient along `affineQuotientFlagMorphism` is the
step-`j` quotient of `F`. -/
def affineQuotientFlagUniversalIso (j : Fin (n+1)) :
    (Scheme.Modules.pullback (affineQuotientFlagMorphism R A F)).obj
      (selectedFlagUniversalTarget R n j) ≅ F.target j :=
  selectedFlagAffineFamilyIso R A (affineQuotientFlagMorphism R A F) F
    (affineQuotientFlagMorphism_step R A F) j

@[reassoc]
theorem affineQuotientFlagUniversalIso_source (j : Fin (n+1)) :
    coordinatePullbackQuotient (affineQuotientFlagMorphism R A F)
        (selectedFlagUniversalQuotient R n j) ≫
      (affineQuotientFlagUniversalIso R A F j).hom = F.quotient j :=
  selectedFlagAffineFamilyIso_source R A (affineQuotientFlagMorphism R A F) F
    (affineQuotientFlagMorphism_step R A F) j

@[reassoc]
theorem affineQuotientFlagUniversalIso_transition (j : Fin n) :
    (Scheme.Modules.pullback (affineQuotientFlagMorphism R A F)).map
        (selectedFlagUniversalTransition R n j) ≫
      (affineQuotientFlagUniversalIso R A F j.succ).hom =
    (affineQuotientFlagUniversalIso R A F j.castSucc).hom ≫ F.transition j :=
  QuotientFlagFamily.transition_natural_of_source
    ((selectedFlagUniversalFamily R n).pullback (affineQuotientFlagMorphism R A F)) F
    (fun j => (affineQuotientFlagUniversalIso R A F j).hom)
    (affineQuotientFlagUniversalIso_source R A F) j

theorem affineQuotientFlagMorphism_unique
    (f : Spec A ⟶ selectedFlagChartScheme R n)
    (hf : f ≫ selectedFlagChartSchemeToSpec R n = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (e : ∀ j, (Scheme.Modules.pullback f).obj (selectedFlagUniversalTarget R n j) ≅ F.target j)
    (he : ∀ j, coordinatePullbackQuotient f (selectedFlagUniversalQuotient R n j) ≫
      (e j).hom = F.quotient j) : f = affineQuotientFlagMorphism R A F := by
  apply selectedFlagUniversalMorphism_unique R f (affineQuotientFlagMorphism R A F)
      (hf.trans (affineQuotientFlagMorphism_toSpec R A F).symm)
      (fun j => e j ≪≫ (affineQuotientFlagUniversalIso R A F j).symm)
  intro j
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, he j, ← affineQuotientFlagUniversalIso_source R A F j]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Every affine quotient-sheaf flag has exactly one classifying map over R. -/
theorem affineQuotientFlagUniversal_existsUnique :
    ∃! f : {f : Spec A ⟶ selectedFlagChartScheme R n //
      f ≫ selectedFlagChartSchemeToSpec R n = Spec.map (CommRingCat.ofHom (algebraMap R A))},
      ∃ e : ∀ j, (Scheme.Modules.pullback f.val).obj (selectedFlagUniversalTarget R n j) ≅
          F.target j,
        ∀ j, coordinatePullbackQuotient f.val (selectedFlagUniversalQuotient R n j) ≫
          (e j).hom = F.quotient j := by
  refine ⟨⟨affineQuotientFlagMorphism R A F, affineQuotientFlagMorphism_toSpec R A F⟩,
    ⟨affineQuotientFlagUniversalIso R A F, affineQuotientFlagUniversalIso_source R A F⟩, ?_⟩
  rintro f ⟨e, he⟩
  exact Subtype.ext (affineQuotientFlagMorphism_unique R A F f.val f.property e he)

end FlagVarieties.Foundations.QuotientCharts
