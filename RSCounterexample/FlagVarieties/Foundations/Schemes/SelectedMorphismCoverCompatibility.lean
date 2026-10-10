import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedMorphismFiniteCover

/-!
# Compatibility of quotient kernels recovered from an incoming map

Any two local presentations of the same incoming scheme map give equal
quotients after extension to a common algebra. This applies in
particular to the tensor-product rings of principal intersections.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts.SelectedMorphismCover

open AlgebraicGeometry CategoryTheory TensorProduct

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {n d : ℕ}
  {F : Spec (CommRingCat.of A) ⟶ selectedChartScheme R n d}
  (D E : SelectedMorphismCover F)

/-- Extending a recovered evaluation gives the pullback of the original map. -/
theorem factors_after_map {B : Type u} [CommRing B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] (i : D.index)
    (g : Localization.Away (D.element i) →ₐ[A] B) :
    selectedChartPointMap R (D.selection i)
        ((g.restrictScalars R).comp (D.evaluation i)) =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ F := by
  rw [← selectedChartPointMap_comp, D.factors, ← Category.assoc]
  congr 1
  exact spec_map_algHom_toSpec A g

/-- Common scalar extensions of two recovered local matrices have equal quotient kernels. -/
theorem quotient_after_maps_eq {B : Type u} [CommRing B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] (i : D.index) (j : E.index)
    (g : Localization.Away (D.element i) →ₐ[A] B)
    (h : Localization.Away (E.element j) →ₐ[A] B) :
    selectedChartPoint R (D.selection i) ((g.restrictScalars R).comp (D.evaluation i)) =
      selectedChartPoint R (E.selection j) ((h.restrictScalars R).comp (E.evaluation j)) := by
  apply selectedChartPoint_quotient_eq_of_map_eq
  rw [D.factors_after_map i g, E.factors_after_map j h]

end FlagVarieties.Foundations.QuotientCharts.SelectedMorphismCover
