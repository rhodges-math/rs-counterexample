import Schubert.FlagVarieties.Foundations.Schemes.GlobalQuotientFlagNaturality

/-! The arbitrary-scheme classifier agrees with the original affine kernel classifier. -/

noncomputable section
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] (A : CommRingCat.{u}) [Algebra R A]
  {n : ℕ} (F : QuotientFlagFamily (Spec A) n)

theorem globalQuotientFlagMorphism_affine :
    globalQuotientFlagMorphism R
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) F =
    simultaneousFlagRelativeMorphism R (F.toRingFlag A) := by
  exact affineQuotientFlagMorphism_unique R A F _
    (globalQuotientFlagMorphism_toSpec R _ F)
    (globalQuotientFlagUniversalIso R _ F)
    (globalQuotientFlagUniversalIso_source R _ F)

end FlagVarieties.Foundations.QuotientCharts
