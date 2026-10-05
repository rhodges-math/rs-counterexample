import Schubert.FlagVarieties.Foundations.Flags.SelectedFlagChartIdeal
import Schubert.FlagVarieties.Foundations.Schemes.SelectedChartSchemeStructure
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The affine closed incidence chart for a complete flag

The spectrum of the joint parameter ring modulo all adjacent incidence
equations is a closed subscheme of the joint affine parameter
space. The quotient ring carries the original nested selected-chart
kernels, with the zero and full endpoints.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] {n : ℕ}
  (a : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)

/-- The affine scheme cut out by all adjacent flag incidence equations. -/
def selectedFlagIncidenceChart : Scheme.{u} :=
  Spec (CommRingCat.of
    (MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R a))

/-- The quotient-ring map is a closed immersion in joint affine parameter space. -/
def selectedFlagIncidenceChartInclusion :
    selectedFlagIncidenceChart R a ⟶
      Spec (CommRingCat.of (MvPolynomial (FlagChartVariable n) R)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (selectedFlagIncidenceIdeal R a)))

instance selectedFlagIncidenceChartInclusion_isClosedImmersion :
    IsClosedImmersion (selectedFlagIncidenceChartInclusion R a) := by
  unfold selectedFlagIncidenceChartInclusion
  exact @IsClosedImmersion.spec_of_quotient_mk
    (CommRingCat.of (MvPolynomial (FlagChartVariable n) R))
    (selectedFlagIncidenceIdeal R a)

/-- The closed flag chart retains its coefficient base. -/
def selectedFlagIncidenceChartToSpec :
    selectedFlagIncidenceChart R a ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R
    (MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R a)))

@[reassoc]
theorem selectedFlagIncidenceChartInclusion_toSpec :
    selectedFlagIncidenceChartInclusion R a ≫
      Spec.map (CommRingCat.ofHom (algebraMap R
        (MvPolynomial (FlagChartVariable n) R))) =
      selectedFlagIncidenceChartToSpec R a := by
  unfold selectedFlagIncidenceChartInclusion selectedFlagIncidenceChartToSpec
  rw [← Spec.map_comp]
  rfl

/-- Each step remembers its own original selected-quotient parameters. -/
def selectedFlagIncidenceChartStep (j : Fin (n+1)) :
    selectedFlagIncidenceChart R a ⟶
      Spec (CommRingCat.of
        (MvPolynomial (Fin (n-j.val) × Fin (n-(n-j.val))) R)) :=
  Spec.map (CommRingCat.ofHom
    (((Ideal.Quotient.mkₐ R (selectedFlagIncidenceIdeal R a)).comp
      (selectedFlagChartVariables R j)).toRingHom))

@[reassoc]
theorem selectedFlagIncidenceChartStep_toSpec (j : Fin (n+1)) :
    selectedFlagIncidenceChartStep R a j ≫
      Spec.map (CommRingCat.ofHom (algebraMap R
        (MvPolynomial (Fin (n-j.val) × Fin (n-(n-j.val))) R))) =
      selectedFlagIncidenceChartToSpec R a := by
  unfold selectedFlagIncidenceChartStep selectedFlagIncidenceChartToSpec
  rw [← Spec.map_comp]
  congr 1
  ext r
  simp
  exact (Ideal.Quotient.mkₐ R (selectedFlagIncidenceIdeal R a)).commutes r

/-- The `j`-th quotient of the universal flag lies in the original
Grassmannian chart selected by `a j`. -/
def selectedFlagIncidenceChartStepMorphism (j : Fin (n+1)) :
    selectedFlagIncidenceChart R a ⟶ selectedChartScheme R n (n-j.val) :=
  selectedFlagIncidenceChartStep R a j ≫
    selectedChartSchemeChart R n (n-j.val) (a j)

@[reassoc]
theorem selectedFlagIncidenceChartStepMorphism_toSpec (j : Fin (n+1)) :
    selectedFlagIncidenceChartStepMorphism R a j ≫
      selectedChartSchemeToSpec R n (n-j.val) =
      selectedFlagIncidenceChartToSpec R a := by
  unfold selectedFlagIncidenceChartStepMorphism
  rw [Category.assoc, selectedChartSchemeChart_toSpec]
  exact selectedFlagIncidenceChartStep_toSpec R a j

end FlagVarieties.Foundations.QuotientCharts
