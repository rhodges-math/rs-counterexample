import Schubert.FlagVarieties.Foundations.Schemes.SelectedFlagMorphismLocalCharts

/-! # Derived principal presentation covers of incoming affine flag morphisms -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ}

/-- A cover of `Spec A` by basic open sets `D(fᵢ)` on each of which the morphism `F : Spec A ⟶ Flₙ`
lands in a chart, together with its chart coordinates there. -/
structure SelectedFlagMorphismCover
    (F : Spec (CommRingCat.of A) ⟶ selectedFlagChartScheme R n) where
  /-- The index set of the cover. -/
  index : Type u
  /-- The functions `fᵢ` whose basic open sets `D(fᵢ)` cover `Spec A`. -/
  element : index → A
  /-- The chart into which `F` maps `D(fᵢ)`. -/
  selection : index → (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n
  span_top : Ideal.span (Set.range element) = ⊤
  /-- The chart coordinates of `F` on `D(fᵢ)`. -/
  evaluation : ∀ i, MvPolynomial (FlagChartVariable n) R →ₐ[R]
    Localization.Away (element i)
  incidence : ∀ i, selectedFlagIncidenceIdeal R (selection i) ≤
    RingHom.ker (evaluation i).toRingHom
  factors : ∀ i, selectedFlagChartPointMap R (selection i) (evaluation i) (incidence i) =
    Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (element i)))) ≫ F

theorem selectedFlagMorphismCover_nonempty
    (F : Spec (CommRingCat.of A) ⟶ selectedFlagChartScheme R n)
    (hF : F ≫ selectedFlagChartSchemeToSpec R n =
      Spec.map (CommRingCat.ofHom (algebraMap R A))) : Nonempty (SelectedFlagMorphismCover F) := by
  classical
  choose s a k hk hmem hfac using selectedFlagMorphism_exists_principal_evaluation R F hF
  refine ⟨{
    index := PrimeSpectrum A
    element := s
    selection := a
    span_top := ?_
    evaluation := k
    incidence := hk
    factors := hfac }⟩
  apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp
  apply top_le_iff.mp
  intro x hx
  exact Opens.mem_iSup.mpr ⟨x, hmem x⟩

/-- A chosen chart cover of a morphism `Spec A ⟶ Flₙ` over `Spec R`. -/
def selectedFlagMorphismCover
    (F : Spec (CommRingCat.of A) ⟶ selectedFlagChartScheme R n)
    (hF : F ≫ selectedFlagChartSchemeToSpec R n =
      Spec.map (CommRingCat.ofHom (algebraMap R A))) : SelectedFlagMorphismCover F :=
  Classical.choice (selectedFlagMorphismCover_nonempty F hF)

namespace SelectedFlagMorphismCover
variable {F : Spec (CommRingCat.of A) ⟶ selectedFlagChartScheme R n}
  (D : SelectedFlagMorphismCover F)

/-- The open cover of `Spec A` by the basic open sets `D(fᵢ)`. -/
abbrev schemeCover : (Spec (CommRingCat.of A)).OpenCover :=
  (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of A) D.element D.span_top).openCover

/-- The restriction of `F` to `D(fᵢ)`, as a point of the chart `selection i`. -/
def chartMap (i : D.index) : Spec (CommRingCat.of (Localization.Away (D.element i))) ⟶
    selectedFlagChartScheme R n :=
  selectedFlagChartPointMap R (D.selection i) (D.evaluation i) (D.incidence i)

@[reassoc]
theorem restriction (i : D.index) : D.schemeCover.f i ≫ F = D.chartMap i :=
  (D.factors i).symm

end SelectedFlagMorphismCover
end FlagVarieties.Foundations.QuotientCharts
