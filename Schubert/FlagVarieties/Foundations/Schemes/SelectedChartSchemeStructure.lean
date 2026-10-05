import Schubert.FlagVarieties.Foundations.Schemes.SelectedChartGlueData

/-!+# The structure morphism of the glued selected-coordinate charts

The regular transition maps preserve the original coefficient ring.
Consequently the glued scheme has a structure morphism to `Spec R`.
The gluing universal property and its uniqueness concern scheme morphisms;
the identification with the quotient Grassmannian functor is
`Schemes/SelectedAffineClassification.lean`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

variable (R : Type u) [CommRing R] (n d : ℕ)

/-- The structure morphism on each affine matrix chart. -/
def selectedChartToSpec :
    Spec (CommRingCat.of (MvPolynomial (Fin d × Fin (n - d)) R)) ⟶
      Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin d × Fin (n - d)) R)))

variable {n d}

/-- The regular transition preserves the base-ring coordinates. -/
theorem selectedChartOverlapMap_toSpec (a b : Fin d ↪ Fin n) :
    selectedChartOverlapMap R a b ≫ selectedChartToSpec R n d =
      selectedChartOverlapInclusion R a b ≫ selectedChartToSpec R n d := by
  rw [selectedChartOverlapMap, matrixOverlapMap, selectedChartToSpec,
    selectedChartOverlapInclusion, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change matrixOverlapCoordinates R (selectedPolynomialBlock R a b)
    (remainingPolynomialBlock R a b) (algebraMap R _ r) =
      algebraMap _ (Localization.Away (selectedPolynomialBlock R a b).det) (algebraMap R _ r)
  rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

variable (n d)

/-- The universal gluing of compatible scheme morphisms out of the charts. -/
def selectedChartSchemeDesc {X : Scheme.{u}}
    (f : (a : Fin d ↪ Fin n) →
      Spec (CommRingCat.of (MvPolynomial (Fin d × Fin (n - d)) R)) ⟶ X)
    (hf : ∀ a b, selectedChartOverlapInclusion R a b ≫ f a =
      selectedChartOverlapMap R a b ≫ f b) : selectedChartScheme R n d ⟶ X :=
  Multicoequalizer.desc (selectedChartGlueData R n d).toGlueData.diagram X
    (fun a => f a.down) (by
      rintro ⟨a, b⟩
      change selectedChartOverlapInclusion R a.down b.down ≫ f a.down =
        ((selectedChartOverlapIso R a.down b.down).hom ≫
          selectedChartOverlapInclusion R b.down a.down) ≫ f b.down
      rw [selectedChartOverlapIso_hom_inclusion]
      exact hf a.down b.down)

@[reassoc] theorem selectedChartSchemeChart_desc {X : Scheme.{u}}
    (f : (a : Fin d ↪ Fin n) →
      Spec (CommRingCat.of (MvPolynomial (Fin d × Fin (n - d)) R)) ⟶ X)
    (hf : ∀ a b, selectedChartOverlapInclusion R a b ≫ f a =
      selectedChartOverlapMap R a b ≫ f b) (a : Fin d ↪ Fin n) :
    selectedChartSchemeChart R n d a ≫ selectedChartSchemeDesc R n d f hf = f a :=
  Multicoequalizer.π_desc (selectedChartGlueData R n d).toGlueData.diagram X
    (fun b => f b.down) _ (ULift.up a)

/-- Maps out of the glued scheme are determined by their chart restrictions. -/
theorem selectedChartScheme_hom_ext {X : Scheme.{u}}
    (f g : selectedChartScheme R n d ⟶ X)
    (h : ∀ a, selectedChartSchemeChart R n d a ≫ f =
      selectedChartSchemeChart R n d a ≫ g) : f = g :=
  Multicoequalizer.hom_ext _ f g (fun a => h a.down)

/-- The glued chart scheme is a scheme over the original coefficient ring. -/
def selectedChartSchemeToSpec : selectedChartScheme R n d ⟶ Spec (CommRingCat.of R) :=
  selectedChartSchemeDesc R n d (fun _ => selectedChartToSpec R n d)
    (fun a b => (selectedChartOverlapMap_toSpec R a b).symm)

@[reassoc] theorem selectedChartSchemeChart_toSpec (a : Fin d ↪ Fin n) :
    selectedChartSchemeChart R n d a ≫ selectedChartSchemeToSpec R n d =
      selectedChartToSpec R n d :=
  selectedChartSchemeChart_desc R n d _ _ a

end FlagVarieties.Foundations.QuotientCharts
