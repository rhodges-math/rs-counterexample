import Schubert.FlagVarieties.Foundations.Schemes.GlobalLocallyFreeQuotient

/-!
# Naturality and uniqueness of global quotient classification

The classifying morphism commutes with arbitrary scheme pullback.
The isomorphism recovering a fixed quotient is uniquely determined by its
equation on the original labelled source.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory ModuleSheafGluing
universe u
variable (R : Type u) [CommRing R] {X : Scheme.{u}} {n : ℕ} {M : X.Modules}
  (b : X ⟶ Spec (CommRingCat.of R))
  (q : coordinateFreeSheaf X n ⟶ M) [Epi q] (d : ℕ)
  (hfree : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty (M.over U ≅
      SheafOfModules.free (R := X.ringCatSheaf.over U) (CoordinateIndex.{u} d)))

/-- The source-preserving universal recovery isomorphism is unique. -/
theorem globalLocallyFreeUniversalIso_unique
    (e : (Scheme.Modules.pullback (globalLocallyFreeQuotientMorphism R b q d hfree)).obj
      (selectedUniversalQuotientSheaf R n d) ≅ M)
    (he : coordinatePullbackQuotient (globalLocallyFreeQuotientMorphism R b q d hfree)
      (selectedUniversalQuotient R n d) ≫ e.hom = q) :
    e = globalLocallyFreeUniversalIso R b q d hfree := by
  apply Iso.ext
  apply (cancel_epi (coordinatePullbackQuotient
    (globalLocallyFreeQuotientMorphism R b q d hfree) (selectedUniversalQuotient R n d))).mp
  exact he.trans (globalLocallyFreeUniversalIso_source R b q d hfree).symm

/-- Arbitrary base change of the quotient gives the composite classifying map. -/
theorem globalLocallyFreeQuotientMorphism_pullback {Y : Scheme.{u}} (f : Y ⟶ X) :
    f ≫ globalLocallyFreeQuotientMorphism R b q d hfree =
      globalLocallyFreeQuotientMorphism R (f ≫ b) (coordinatePullbackQuotient f q) d
        (coordinateLocalFrames_pullback f M d hfree) := by
  apply globalLocallyFreeQuotientMorphism_unique R (f ≫ b) (coordinatePullbackQuotient f q) d
    (coordinateLocalFrames_pullback f M d hfree)
    (f ≫ globalLocallyFreeQuotientMorphism R b q d hfree)
    (by rw [Category.assoc, globalLocallyFreeQuotientMorphism_toSpec])
    (coordinateQuotientComparisonPullback f (globalLocallyFreeQuotientMorphism R b q d hfree)
      (globalLocallyFreeUniversalIso R b q d hfree))
  exact coordinateQuotientComparisonPullback_source f
    (globalLocallyFreeQuotientMorphism R b q d hfree) (selectedUniversalQuotient R n d) q
    (globalLocallyFreeUniversalIso R b q d hfree)
    (globalLocallyFreeUniversalIso_source R b q d hfree)

/-- Isomorphic quotients of the same labelled source have the same classifying map. -/
theorem globalLocallyFreeQuotientMorphism_targetIso {N : X.Modules}
    (r : coordinateFreeSheaf X n ⟶ N) [Epi r]
    (hN : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (N.over U ≅
        SheafOfModules.free (R := X.ringCatSheaf.over U) (CoordinateIndex.{u} d)))
    (e : M ≅ N) (he : q ≫ e.hom = r) :
    globalLocallyFreeQuotientMorphism R b q d hfree =
      globalLocallyFreeQuotientMorphism R b r d hN := by
  apply globalLocallyFreeQuotientMorphism_unique R b r d hN
    (globalLocallyFreeQuotientMorphism R b q d hfree)
    (globalLocallyFreeQuotientMorphism_toSpec R b q d hfree)
    (globalLocallyFreeUniversalIso R b q d hfree ≪≫ e)
  simp only [Iso.trans_hom]
  rw [← Category.assoc, globalLocallyFreeUniversalIso_source, he]

end FlagVarieties.Foundations.QuotientCharts
