import Schubert.FlagVarieties.Foundations.Schemes.AffineLocallyFreeUniversalClassification
import Schubert.FlagVarieties.Foundations.Schemes.CoordinateLocalFramesPullback

/-!
# Local classifying maps on every incoming affine scheme

The structural map to the coefficient spectrum supplies its own algebra
structure. The quotient and its local frames are pulled back from the
given scheme; no affine presentation or basis is an additional input.
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
  (A : CommRingCat.{u}) (h : Spec A ⟶ X)

/-- Classifying morphism of the pullback quotient on any affine source. -/
def locallyFreeQuotientAffineMorphism : Spec A ⟶ selectedChartScheme R n d := by
  letI : Algebra R A := ((Spec.fullyFaithful.preimage (h ≫ b)).unop.hom).toAlgebra
  exact affineLocallyFreeQuotientMorphism R A (coordinatePullbackQuotient h q) d
    (coordinateLocalFrames_pullback h M d hfree)

@[reassoc]
theorem locallyFreeQuotientAffineMorphism_toSpec :
    locallyFreeQuotientAffineMorphism R b q d hfree A h ≫
      selectedChartSchemeToSpec R n d = h ≫ b := by
  let : Algebra R A := ((Spec.fullyFaithful.preimage (h ≫ b)).unop.hom).toAlgebra
  unfold locallyFreeQuotientAffineMorphism
  rw [affineLocallyFreeQuotientMorphism_toSpec]
  exact Spec.map_preimage_unop (h ≫ b)

/-- Universal quotient recovery retains the original pulled-back target. -/
def locallyFreeQuotientAffineIso :
    (Scheme.Modules.pullback (locallyFreeQuotientAffineMorphism R b q d hfree A h)).obj
        (selectedUniversalQuotientSheaf R n d) ≅
      (Scheme.Modules.pullback h).obj M := by
  letI : Algebra R A := ((Spec.fullyFaithful.preimage (h ≫ b)).unop.hom).toAlgebra
  exact affineLocallyFreeUniversalQuotientIso R A (coordinatePullbackQuotient h q) d
    (coordinateLocalFrames_pullback h M d hfree)

@[reassoc]
theorem locallyFreeQuotientAffineIso_source :
    coordinatePullbackQuotient (locallyFreeQuotientAffineMorphism R b q d hfree A h)
        (selectedUniversalQuotient R n d) ≫
      (locallyFreeQuotientAffineIso R b q d hfree A h).hom =
      coordinatePullbackQuotient h q := by
  let : Algebra R A := ((Spec.fullyFaithful.preimage (h ≫ b)).unop.hom).toAlgebra
  exact affineLocallyFreeUniversalQuotientIso_source R A (coordinatePullbackQuotient h q) d
    (coordinateLocalFrames_pullback h M d hfree)

end FlagVarieties.Foundations.QuotientCharts
