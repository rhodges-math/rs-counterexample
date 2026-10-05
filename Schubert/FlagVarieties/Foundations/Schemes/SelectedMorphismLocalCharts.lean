import Schubert.FlagVarieties.Foundations.Schemes.SelectedQuotientMorphismPresentation
import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# Principal local chart presentations of arbitrary incoming morphisms

The selected charts cover the glued scheme. Pulling back their open
images and taking principal neighborhoods on an affine source gives
local factorizations. The scalar condition on an incoming map then recovers
algebra homomorphisms, not just pointwise coordinate functions.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

variable (R : Type u) [CommRing R] {A : Type u} [CommRing A]
  {n d : ℕ}

/-- Every point has a principal neighborhood on which an incoming map factors through a chart. -/
theorem selectedMorphism_exists_principal_chart
    (F : Spec (CommRingCat.of A) ⟶ selectedChartScheme R n d) (x : PrimeSpectrum A) :
    ∃ (s : A) (a : Fin d ↪ Fin n)
      (f : Spec (CommRingCat.of (Localization.Away s)) ⟶
        Spec (CommRingCat.of (MvPolynomial (Fin d × Fin (n - d)) R))),
      x ∈ PrimeSpectrum.basicOpen s ∧
        f ≫ selectedChartSchemeChart R n d a =
          Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away s))) ≫ F := by
  obtain ⟨a, y, hy⟩ := selectedChartSchemeChart_jointly_surjective R n d (F x)
  have hx : x ∈ F ⁻¹' Set.range (selectedChartSchemeChart R n d a) := ⟨y, hy⟩
  have ho : IsOpen (F ⁻¹' Set.range (selectedChartSchemeChart R n d a)) :=
    (IsOpenImmersion.isOpen_range (selectedChartSchemeChart R n d a)).preimage F.continuous
  obtain ⟨V, ⟨s, rfl⟩, hxs, hs⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx ho
  have hr : Set.range
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away s))) ≫ F) ⊆
        Set.range (selectedChartSchemeChart R n d a) := by
    rintro _ ⟨z, rfl⟩
    apply hs
    exact (PrimeSpectrum.localization_away_comap_range (Localization.Away s) s).le ⟨z, rfl⟩
  exact ⟨s, a, IsOpenImmersion.lift (selectedChartSchemeChart R n d a) _ hr,
    hxs, IsOpenImmersion.lift_fac _ _ hr⟩

variable [Algebra R A]

/-- A map from an affine source to a selected chart over R gives its polynomial evaluation. -/
def selectedAffineChartEvaluation
    (f : Spec (CommRingCat.of A) ⟶
      Spec (CommRingCat.of (MvPolynomial (Fin d × Fin (n - d)) R)))
    (hf : f ≫ selectedChartToSpec R n d =
      Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A :=
  { (Spec.preimage f).hom with
    commutes' := fun r =>
      RingHom.congr_fun (spec_preimage_comp_eq (algebraMap R _) f (algebraMap R A) hf) r }

/-- Recovering the algebra map retains the complete affine scheme morphism. -/
theorem selectedAffineChartEvaluation_spec
    (f : Spec (CommRingCat.of A) ⟶
      Spec (CommRingCat.of (MvPolynomial (Fin d × Fin (n - d)) R)))
    (hf : f ≫ selectedChartToSpec R n d =
      Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    Spec.map (CommRingCat.ofHom (selectedAffineChartEvaluation R f hf).toRingHom) = f :=
  Spec.map_preimage f

/-- An incoming map over the coefficient base has polynomial evaluations locally. -/
theorem selectedMorphism_exists_principal_evaluation
    (F : Spec (CommRingCat.of A) ⟶ selectedChartScheme R n d)
    (hF : F ≫ selectedChartSchemeToSpec R n d =
      Spec.map (CommRingCat.ofHom (algebraMap R A))) (x : PrimeSpectrum A) :
    ∃ (s : A) (a : Fin d ↪ Fin n)
      (f : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] Localization.Away s),
      x ∈ PrimeSpectrum.basicOpen s ∧
        selectedChartPointMap R a f =
          Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away s))) ≫ F := by
  obtain ⟨s, a, f, hxs, hf⟩ := selectedMorphism_exists_principal_chart R F x
  have hfR : f ≫ selectedChartToSpec R n d =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away s))) := by
    calc
      f ≫ selectedChartToSpec R n d =
          (f ≫ selectedChartSchemeChart R n d a) ≫ selectedChartSchemeToSpec R n d := by
        rw [Category.assoc, selectedChartSchemeChart_toSpec]
      _ = Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away s))) ≫
          F ≫ selectedChartSchemeToSpec R n d := by rw [hf, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away s))) := by
        rw [hF]
        exact spec_map_algHom_toSpec R (IsScalarTower.toAlgHom R A (Localization.Away s))
  refine ⟨s, a, selectedAffineChartEvaluation R f hfR, hxs, ?_⟩
  unfold selectedChartPointMap
  rw [selectedAffineChartEvaluation_spec]
  exact hf

end FlagVarieties.Foundations.QuotientCharts
