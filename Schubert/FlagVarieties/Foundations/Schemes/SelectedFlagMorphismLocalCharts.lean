import Schubert.FlagVarieties.Foundations.Schemes.SelectedFlagChartPointBaseChange
import Schubert.FlagVarieties.Foundations.Schemes.SelectedChartPointFaithfulness
import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# Principal incidence-chart presentations of incoming flag morphisms

The open chart cover supplies local factorizations of every incoming
affine scheme map. Fullness of Spec recovers joint parameters, and the
incidence equations follow from the chart's quotient ring.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable (R : Type u) [CommRing R] {A : Type u} [CommRing A] {n : ℕ}

theorem selectedFlagMorphism_exists_principal_chart
    (F : Spec (CommRingCat.of A) ⟶ selectedFlagChartScheme R n) (x : PrimeSpectrum A) :
    ∃ (s : A) (a : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)
      (f : Spec (CommRingCat.of (Localization.Away s)) ⟶ selectedFlagIncidenceChart R a),
      x ∈ PrimeSpectrum.basicOpen s ∧
        f ≫ selectedFlagChartSchemeChart R n a =
          Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away s))) ≫ F := by
  obtain ⟨a, y, hy⟩ := (selectedFlagChartGlueData R n).ι_jointly_surjective (F x)
  have hx : x ∈ F ⁻¹' Set.range (selectedFlagChartSchemeChart R n a.down) := ⟨y, hy⟩
  have ho : IsOpen (F ⁻¹' Set.range (selectedFlagChartSchemeChart R n a.down)) :=
    (IsOpenImmersion.isOpen_range (selectedFlagChartSchemeChart R n a.down)).preimage F.continuous
  obtain ⟨V, ⟨s, rfl⟩, hxs, hs⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx ho
  have hr : Set.range
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away s))) ≫ F) ⊆
        Set.range (selectedFlagChartSchemeChart R n a.down) := by
    rintro _ ⟨z, rfl⟩
    apply hs
    exact (PrimeSpectrum.localization_away_comap_range (Localization.Away s) s).le ⟨z, rfl⟩
  exact ⟨s, a.down, IsOpenImmersion.lift (selectedFlagChartSchemeChart R n a.down) _ hr,
    hxs, IsOpenImmersion.lift_fac _ _ hr⟩

variable [Algebra R A]
  (a : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)

/-- A chart map over R determines its incidence-quotient algebra map. -/
def selectedFlagAffineChartEvaluation
    (f : Spec (CommRingCat.of A) ⟶ selectedFlagIncidenceChart R a)
    (hf : f ≫ selectedFlagIncidenceChartToSpec R a =
      Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    (MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R a) →ₐ[R] A :=
  { (Spec.preimage f).hom with
    commutes' := fun r =>
      RingHom.congr_fun (spec_preimage_comp_eq (algebraMap R _) f (algebraMap R A) hf) r }

theorem selectedFlagAffineChartEvaluation_spec
    (f : Spec (CommRingCat.of A) ⟶ selectedFlagIncidenceChart R a)
    (hf : f ≫ selectedFlagIncidenceChartToSpec R a =
      Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    Spec.map (CommRingCat.ofHom (selectedFlagAffineChartEvaluation R a f hf).toRingHom) = f :=
  Spec.map_preimage f

theorem selectedFlagAffineChart_exists_parameters
    (f : Spec (CommRingCat.of A) ⟶ selectedFlagIncidenceChart R a)
    (hf : f ≫ selectedFlagIncidenceChartToSpec R a =
      Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    ∃ (k : MvPolynomial (FlagChartVariable n) R →ₐ[R] A)
      (hk : selectedFlagIncidenceIdeal R a ≤ RingHom.ker k.toRingHom),
      selectedFlagChartPointMap R a k hk = f ≫ selectedFlagChartSchemeChart R n a := by
  let e := selectedFlagAffineChartEvaluation R a f hf
  let k := e.comp (Ideal.Quotient.mkₐ R (selectedFlagIncidenceIdeal R a))
  have hk : selectedFlagIncidenceIdeal R a ≤ RingHom.ker k.toRingHom := by
    intro p hp
    change e (Ideal.Quotient.mk (selectedFlagIncidenceIdeal R a) p) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
  have he : selectedFlagIncidenceEvaluation R a k hk = e := by
    apply AlgHom.ext
    intro z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    rfl
  refine ⟨k, hk, ?_⟩
  rw [selectedFlagChartPointMap, he]
  rw [show Spec.map (CommRingCat.ofHom e.toRingHom) = f from
    selectedFlagAffineChartEvaluation_spec R a f hf]

theorem selectedFlagMorphism_exists_principal_evaluation
    (F : Spec (CommRingCat.of A) ⟶ selectedFlagChartScheme R n)
    (hF : F ≫ selectedFlagChartSchemeToSpec R n =
      Spec.map (CommRingCat.ofHom (algebraMap R A))) (x : PrimeSpectrum A) :
    ∃ (s : A) (a : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)
      (k : MvPolynomial (FlagChartVariable n) R →ₐ[R] Localization.Away s)
      (hk : selectedFlagIncidenceIdeal R a ≤ RingHom.ker k.toRingHom),
      x ∈ PrimeSpectrum.basicOpen s ∧
        selectedFlagChartPointMap R a k hk =
          Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away s))) ≫ F := by
  obtain ⟨s, a, f, hxs, hf⟩ := selectedFlagMorphism_exists_principal_chart R F x
  have hfR : f ≫ selectedFlagIncidenceChartToSpec R a =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away s))) := by
    calc
      f ≫ selectedFlagIncidenceChartToSpec R a =
          (f ≫ selectedFlagChartSchemeChart R n a) ≫ selectedFlagChartSchemeToSpec R n := by
        rw [Category.assoc, selectedFlagChartSchemeChart_toSpec]
      _ = Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away s))) ≫
          F ≫ selectedFlagChartSchemeToSpec R n := by rw [hf, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away s))) := by
        rw [hF]
        exact spec_map_algHom_toSpec R (IsScalarTower.toAlgHom R A (Localization.Away s))
  obtain ⟨k, hk, he⟩ := selectedFlagAffineChart_exists_parameters R a f hfR
  exact ⟨s, a, k, hk, hxs, he.trans hf⟩

end FlagVarieties.Foundations.QuotientCharts
