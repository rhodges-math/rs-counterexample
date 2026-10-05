import Schubert.FlagVarieties.Foundations.Schemes.AffineLocallyFreeCoordinateClassification
import Schubert.FlagVarieties.Foundations.Schemes.SelectedQuotientMorphism

/-!
# The classifying morphism of an affine locally free quotient

The input is an epimorphism of module sheaves with locally trivial
rank-d target. Its original coordinate kernel defines a morphism to the
glued Grassmannian chart scheme. Source-preserving isomorphisms of
the target leave this morphism unchanged.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] (A : CommRingCat.{u}) [Algebra R A]
  {n : ℕ} {M : (Spec A).Modules}
  (q : coordinateFreeSheaf (Spec A) n ⟶ M) [Epi q] (d : ℕ)
  (hfree : ∀ p : Spec A, ∃ U : (Spec A).Opens, p ∈ U ∧
    Nonempty (M.over U ≅
      SheafOfModules.free (R := (Spec A).ringCatSheaf.over U) (CoordinateIndex.{u} d)))

/-- The affine classifying morphism obtained from the original quotient kernel. -/
def affineLocallyFreeQuotientMorphism : Spec A ⟶ selectedChartScheme R n d :=
  selectedQuotientMorphism R (affineLocallyFreeGrassmannian A q d hfree)

@[reassoc]
theorem affineLocallyFreeQuotientMorphism_toSpec :
    affineLocallyFreeQuotientMorphism R A q d hfree ≫ selectedChartSchemeToSpec R n d =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) :=
  selectedQuotientMorphism_toSpec

/-- Changing the quotient target while retaining its labelled source preserves the point. -/
theorem affineLocallyFreeGrassmannian_target_iso {N : (Spec A).Modules}
    (r : coordinateFreeSheaf (Spec A) n ⟶ N) [Epi r]
    (hfreeN : ∀ p : Spec A, ∃ U : (Spec A).Opens, p ∈ U ∧
      Nonempty (N.over U ≅
        SheafOfModules.free (R := (Spec A).ringCatSheaf.over U) (CoordinateIndex.{u} d)))
    (e : M ≅ N) (he : q ≫ e.hom = r) :
    affineLocallyFreeGrassmannian A q d hfree = affineLocallyFreeGrassmannian A r d hfreeN := by
  apply affineLocallyFreeGrassmannian_unique A r d hfreeN
    (affineLocallyFreeGrassmannian A q d hfree)
    (affineLocallyFreeGrassmannianSheafIso A q d hfree ≪≫ e)
  rw [Iso.trans_hom, ← Category.assoc, affineLocallyFreeGrassmannianSheafIso_source, he]

theorem affineLocallyFreeQuotientMorphism_target_iso {N : (Spec A).Modules}
    (r : coordinateFreeSheaf (Spec A) n ⟶ N) [Epi r]
    (hfreeN : ∀ p : Spec A, ∃ U : (Spec A).Opens, p ∈ U ∧
      Nonempty (N.over U ≅
        SheafOfModules.free (R := (Spec A).ringCatSheaf.over U) (CoordinateIndex.{u} d)))
    (e : M ≅ N) (he : q ≫ e.hom = r) :
    affineLocallyFreeQuotientMorphism R A q d hfree =
      affineLocallyFreeQuotientMorphism R A r d hfreeN :=
  congrArg (selectedQuotientMorphism R)
    (affineLocallyFreeGrassmannian_target_iso A q d hfree r hfreeN e he)

end FlagVarieties.Foundations.QuotientCharts
