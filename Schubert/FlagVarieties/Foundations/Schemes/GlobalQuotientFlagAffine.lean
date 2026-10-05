import Schubert.FlagVarieties.Foundations.Schemes.AffineQuotientFlagClassification

/-!
# Local classifying maps of flags on arbitrary scheme bases

Any affine map into the given base pulls back the quotient-sheaf flag.
Its scalar structure is determined by the specified map to Spec R. Thus the
local classifying map and its original-source comparisons require no supplied
frames or incidence-chart choices.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] {X : Scheme.{u}} {n : ℕ}
  (b : X ⟶ Spec (CommRingCat.of R)) (F : QuotientFlagFamily X n)
  (A : CommRingCat.{u}) (h : Spec A ⟶ X)

/-- For an affine scheme `Spec A ⟶ X`, the morphism `Spec A ⟶ Flₙ` classifying the pullback of the
quotient flag family `F`. -/
def quotientFlagAffineMorphism : Spec A ⟶ selectedFlagChartScheme R n := by
  letI : Algebra R A := ((Spec.fullyFaithful.preimage (h ≫ b)).unop.hom).toAlgebra
  exact affineQuotientFlagMorphism R A (F.pullback h)

@[reassoc]
theorem quotientFlagAffineMorphism_toSpec :
    quotientFlagAffineMorphism R b F A h ≫ selectedFlagChartSchemeToSpec R n = h ≫ b := by
  let : Algebra R A := ((Spec.fullyFaithful.preimage (h ≫ b)).unop.hom).toAlgebra
  unfold quotientFlagAffineMorphism
  rw [affineQuotientFlagMorphism_toSpec]
  exact Spec.map_preimage_unop (h ≫ b)

/-- The pullback of the universal step-`j` quotient along `quotientFlagAffineMorphism` is the
pullback of the step-`j` quotient of `F`. -/
def quotientFlagAffineIso (j : Fin (n+1)) :
    (Scheme.Modules.pullback (quotientFlagAffineMorphism R b F A h)).obj
      (selectedFlagUniversalTarget R n j) ≅
    (Scheme.Modules.pullback h).obj (F.target j) := by
  letI : Algebra R A := ((Spec.fullyFaithful.preimage (h ≫ b)).unop.hom).toAlgebra
  exact affineQuotientFlagUniversalIso R A (F.pullback h) j

@[reassoc]
theorem quotientFlagAffineIso_source (j : Fin (n+1)) :
    coordinatePullbackQuotient (quotientFlagAffineMorphism R b F A h)
        (selectedFlagUniversalQuotient R n j) ≫
      (quotientFlagAffineIso R b F A h j).hom =
        coordinatePullbackQuotient h (F.quotient j) := by
  let : Algebra R A := ((Spec.fullyFaithful.preimage (h ≫ b)).unop.hom).toAlgebra
  exact affineQuotientFlagUniversalIso_source R A (F.pullback h) j

end FlagVarieties.Foundations.QuotientCharts
