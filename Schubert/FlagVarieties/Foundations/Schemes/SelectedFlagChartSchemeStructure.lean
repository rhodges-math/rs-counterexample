import Schubert.FlagVarieties.Foundations.Schemes.SelectedFlagChartGlueData

/-! # The base morphism and outgoing universal property of the glued flag charts -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : Type u) [CommRing R] (n : ℕ)

/-- Compatible morphisms on all incidence charts glue to a scheme morphism. -/
def selectedFlagChartSchemeDesc {X : Scheme.{u}}
    (f : (a : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n) → selectedFlagIncidenceChart R a ⟶ X)
    (hf : ∀ a b, selectedFlagOverlapInclusion R a b ≫ f a = selectedFlagOverlapMap R a b ≫ f b) :
    selectedFlagChartScheme R n ⟶ X :=
  Multicoequalizer.desc (selectedFlagChartGlueData R n).toGlueData.diagram X
    (fun a => f a.down) (by
      rintro ⟨a, b⟩
      change selectedFlagOverlapInclusion R a.down b.down ≫ f a.down =
        ((selectedFlagOverlapSchemeIso R a.down b.down).hom ≫
          selectedFlagOverlapInclusion R b.down a.down) ≫ f b.down
      rw [selectedFlagOverlapSchemeIso_hom_inclusion]
      exact hf a.down b.down)

@[reassoc]
theorem selectedFlagChartSchemeChart_desc {X : Scheme.{u}}
    (f : (a : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n) → selectedFlagIncidenceChart R a ⟶ X)
    (hf : ∀ a b, selectedFlagOverlapInclusion R a b ≫ f a = selectedFlagOverlapMap R a b ≫ f b)
    (a : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n) :
    selectedFlagChartSchemeChart R n a ≫ selectedFlagChartSchemeDesc R n f hf = f a :=
  Multicoequalizer.π_desc (selectedFlagChartGlueData R n).toGlueData.diagram X
    (fun b => f b.down) _ (ULift.up a)

theorem selectedFlagChartScheme_hom_ext {X : Scheme.{u}}
    (f g : selectedFlagChartScheme R n ⟶ X)
    (h : ∀ a, selectedFlagChartSchemeChart R n a ≫ f = selectedFlagChartSchemeChart R n a ≫ g) :
    f = g :=
  Multicoequalizer.hom_ext _ f g (fun a => h a.down)

/-- The glued incidence scheme lies over the original coefficient ring. -/
def selectedFlagChartSchemeToSpec : selectedFlagChartScheme R n ⟶ Spec (CommRingCat.of R) :=
  selectedFlagChartSchemeDesc R n (fun a => selectedFlagIncidenceChartToSpec R a)
    (fun a b => (selectedFlagOverlapMap_toSpec R a b).symm)

@[reassoc]
theorem selectedFlagChartSchemeChart_toSpec
    (a : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n) :
    selectedFlagChartSchemeChart R n a ≫ selectedFlagChartSchemeToSpec R n =
      selectedFlagIncidenceChartToSpec R a :=
  selectedFlagChartSchemeChart_desc R n _ _ a

end FlagVarieties.Foundations.QuotientCharts
