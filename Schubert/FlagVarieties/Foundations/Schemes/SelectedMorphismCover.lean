import Schubert.FlagVarieties.Foundations.Schemes.SelectedMorphismLocalCharts

/-!
# Principal presentation covers of incoming affine scheme maps

The local matrices are recovered from an arbitrary map over the coefficient
base using the open charts and the fully faithful Spec functor.
The cover and all local factorization equations are proved to exist.
No global quotient is assumed or supplied by these data.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {n d : ℕ}

/-- Principal local polynomial evaluations of a specified incoming map. -/
structure SelectedMorphismCover
    (F : Spec (CommRingCat.of A) ⟶ selectedChartScheme R n d) where
  /-- The index set of the cover. -/
  index : Type u
  /-- The functions `fᵢ` whose basic open sets `D(fᵢ)` cover `Spec A`. -/
  element : index → A
  /-- The chart into which `F` maps `D(fᵢ)`. -/
  selection : index → (Fin d ↪ Fin n)
  span_top : Ideal.span (Set.range element) = ⊤
  /-- The chart coordinates of `F` on `D(fᵢ)`. -/
  evaluation : ∀ i, MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R]
    Localization.Away (element i)
  factors : ∀ i, selectedChartPointMap R (selection i) (evaluation i) =
    Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (element i)))) ≫ F

/-- Every incoming map over R has such a cover, without a supplied quotient or local frames. -/
theorem selectedMorphismCover_nonempty
    (F : Spec (CommRingCat.of A) ⟶ selectedChartScheme R n d)
    (hF : F ≫ selectedChartSchemeToSpec R n d =
      Spec.map (CommRingCat.ofHom (algebraMap R A))) : Nonempty (SelectedMorphismCover F) := by
  classical
  choose s a f hmem hfac using selectedMorphism_exists_principal_evaluation R F hF
  refine ⟨{
    index := PrimeSpectrum A
    element := s
    selection := a
    span_top := ?_
    evaluation := f
    factors := hfac }⟩
  apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp
  apply top_le_iff.mp
  intro x hx
  exact Opens.mem_iSup.mpr ⟨x, hmem x⟩

/-- A choice of the locally derived presentations. The global quotient they
present is constructed in `Schemes/SelectedMorphismQuotient.lean`. -/
def selectedMorphismCover
    (F : Spec (CommRingCat.of A) ⟶ selectedChartScheme R n d)
    (hF : F ≫ selectedChartSchemeToSpec R n d =
      Spec.map (CommRingCat.ofHom (algebraMap R A))) : SelectedMorphismCover F :=
  Classical.choice (selectedMorphismCover_nonempty F hF)

end FlagVarieties.Foundations.QuotientCharts
