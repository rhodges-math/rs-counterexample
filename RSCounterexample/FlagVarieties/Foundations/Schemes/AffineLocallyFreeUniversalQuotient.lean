import RSCounterexample.FlagVarieties.Foundations.Schemes.AffineLocallyFreeQuotientMorphism
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedUniversalAffineQuotientComparison

/-!
# The universal quotient recovers every affine locally free quotient

The classifying morphism was constructed from the original coordinate
kernel. Its pullback of the universal sheaf is identified with
the given sheaf, preserving the original labelled quotient map. The
source equation makes this isomorphism unique.
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

/-- Pullback of the universal target is the original quotient sheaf. -/
def affineLocallyFreeUniversalQuotientIso :
    (Scheme.Modules.pullback (affineLocallyFreeQuotientMorphism R A q d hfree)).obj
      (selectedUniversalQuotientSheaf R n d) ≅ M :=
  selectedUniversalAffineQuotientIso R A (affineLocallyFreeGrassmannian A q d hfree) ≪≫
    affineLocallyFreeGrassmannianSheafIso A q d hfree

@[reassoc]
theorem affineLocallyFreeUniversalQuotientIso_source :
    coordinatePullbackQuotient (affineLocallyFreeQuotientMorphism R A q d hfree)
        (selectedUniversalQuotient R n d) ≫
      (affineLocallyFreeUniversalQuotientIso R A q d hfree).hom = q := by
  change selectedUniversalAffinePullbackQuotient R A
      (affineLocallyFreeGrassmannian A q d hfree) ≫
    ((selectedUniversalAffineQuotientIso R A
      (affineLocallyFreeGrassmannian A q d hfree)).hom ≫
      (affineLocallyFreeGrassmannianSheafIso A q d hfree).hom) = q
  rw [← Category.assoc, selectedUniversalAffineQuotientIso_source]
  exact affineLocallyFreeGrassmannianSheafIso_source A q d hfree

theorem affineLocallyFreeUniversalQuotientIso_unique
    (e : (Scheme.Modules.pullback (affineLocallyFreeQuotientMorphism R A q d hfree)).obj
      (selectedUniversalQuotientSheaf R n d) ≅ M)
    (he : coordinatePullbackQuotient (affineLocallyFreeQuotientMorphism R A q d hfree)
      (selectedUniversalQuotient R n d) ≫ e.hom = q) :
    e = affineLocallyFreeUniversalQuotientIso R A q d hfree :=
  ModuleSheafGluing.quotientIso_unique
    (coordinatePullbackQuotient (affineLocallyFreeQuotientMorphism R A q d hfree)
      (selectedUniversalQuotient R n d)) q e _ he
    (affineLocallyFreeUniversalQuotientIso_source R A q d hfree)

end FlagVarieties.Foundations.QuotientCharts
