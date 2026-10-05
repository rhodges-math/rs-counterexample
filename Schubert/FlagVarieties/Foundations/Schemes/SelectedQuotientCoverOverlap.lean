import Schubert.FlagVarieties.Foundations.Schemes.SelectedQuotientCover
import Schubert.FlagVarieties.Foundations.Flags.CoordinateSelectedPointNaturality

/-!
# Compatibility of quotient presentations on principal intersections

The comparison is derived from equality of the scalar-extended quotient.
In particular it is not an extra field of the presentation-cover data.
The intersection uses a tensor product over the source ring, so it retains
all scheme structure over arbitrary commutative coefficient rings.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts.SelectedQuotientCover

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {n d : ℕ} {P : Module.Grassmannian A (Fin n → A) d}
  (D E : SelectedQuotientCover R A P)

/-- Every extension of a local presentation represents the extended quotient. -/
theorem represents_after_map {B : Type u} [CommRing B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] (i : D.index)
    (g : Localization.Away (D.element i) →ₐ[A] B) :
    selectedChartPoint R (D.selection i) ((g.restrictScalars R).comp (D.evaluation i)) =
      coordinateGrassmannianBaseChange B P := by
  let : Algebra (Localization.Away (D.element i)) B := g.toAlgebra
  let : IsScalarTower A (Localization.Away (D.element i)) B :=
    IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  rw [← selectedChartPoint_baseChange R (g.restrictScalars R), D.represents,
    coordinateGrassmannianBaseChange_tower]

/-- Coordinate ring of a mixed intersection, for two independently chosen covers. -/
abbrev overlapRing (i : D.index) (j : E.index) :=
  Localization.Away (D.element i) ⊗[A] Localization.Away (E.element j)

/-- The two maps from the tensor-product intersection agree. -/
theorem tensor_overlap (i : D.index) (j : E.index) :
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : Localization.Away (D.element i) →ₐ[A]
        overlapRing D E i j).toRingHom) ≫ D.chartMap i =
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : Localization.Away (E.element j) →ₐ[A]
        overlapRing D E i j).toRingHom) ≫ E.chartMap j := by
  let g : Localization.Away (D.element i) →ₐ[A] overlapRing D E i j :=
    Algebra.TensorProduct.includeLeft
  let h : Localization.Away (E.element j) →ₐ[A] overlapRing D E i j :=
    Algebra.TensorProduct.includeRight
  change Spec.map (CommRingCat.ofHom (g.restrictScalars R).toRingHom) ≫
      selectedChartPointMap R (D.selection i) (D.evaluation i) =
    Spec.map (CommRingCat.ofHom (h.restrictScalars R).toRingHom) ≫
      selectedChartPointMap R (E.selection j) (E.evaluation j)
  rw [selectedChartPointMap_comp, selectedChartPointMap_comp]
  apply selectedChartPointMap_eq_of_quotient_eq
  rw [D.represents_after_map i g, E.represents_after_map j h]

/-- Compatibility holds on the categorical fiber product of principal opens. -/
theorem overlap (i : D.index) (j : E.index) :
    pullback.fst (D.schemeCover.f i) (E.schemeCover.f j) ≫ D.chartMap i =
      pullback.snd (D.schemeCover.f i) (E.schemeCover.f j) ≫ E.chartMap j := by
  change pullback.fst
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (D.element i)))))
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (E.element j))))) ≫
        D.chartMap i =
    pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (D.element i)))))
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (E.element j))))) ≫
        E.chartMap j
  apply (cancel_epi (pullbackSpecIso A (Localization.Away (D.element i))
    (Localization.Away (E.element j))).inv).mp
  rw [← Category.assoc, ← Category.assoc,
    pullbackSpecIso_inv_fst, pullbackSpecIso_inv_snd]
  exact D.tensor_overlap E i j

end FlagVarieties.Foundations.QuotientCharts.SelectedQuotientCover
