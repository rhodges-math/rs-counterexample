import RSCounterexample.FlagVarieties.Foundations.Schemes.SimultaneousFlagCoordinatePointMap
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedFlagChartPointFaithfulness
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedFlagChartPointBaseChange

/-!
# Overlap compatibility of a flag's simultaneous coordinate charts

The local point maps on two product-denominator opens agree over their
tensor-product intersection, because both classify the same original
quotient flag after base change.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct

universe u

variable {A : Type u} [CommRing A] {n : ℕ}
  (F : RingFlag A (Fin n → A) n)

/-- The local map as a point of the glued flag scheme. -/
def simultaneousFlagLocalMap (i : SimultaneousFlagCoordinateIndex F) :
    Spec (CommRingCat.of (Localization.Away (simultaneousFlagCoordinateElement F i))) ⟶
      selectedFlagChartScheme A n :=
  simultaneousFlagIncidencePointMap F i ≫
    selectedFlagChartSchemeChart A n (simultaneousFlagCoordinateSelection F i)

theorem simultaneousFlagLocalMap_eq_pointMap (i : SimultaneousFlagCoordinateIndex F) :
    simultaneousFlagLocalMap F i =
      selectedFlagChartPointMap A (simultaneousFlagCoordinateSelection F i)
        (simultaneousFlagCoordinateEvaluation F i)
        (simultaneousFlagCoordinateEvaluation_ideal F i) := by
  rfl

/-- Scalar extension of joint selected parameters extends every
Grassmannian quotient step, in its original ambient coordinates. -/
theorem selectedFlagChartStep_comp {B C : Type u} [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (a : (j : Fin (n + 1)) → Fin (n - j.val) ↪ Fin n)
    (k : MvPolynomial (FlagChartVariable n) A →ₐ[A] B)
    (g : B →ₐ[A] C) (j : Fin (n + 1)) :
    selectedFlagChartStep A a (g.comp k) j =
      letI : Algebra B C := g.toAlgebra
      coordinateGrassmannianBaseChange C (selectedFlagChartStep A a k j) := by
  letI : Algebra B C := g.toAlgebra
  unfold selectedFlagChartStep
  rw [AlgHom.comp_assoc]
  exact (selectedChartPoint_baseChange A g (a j)
    (k.comp (selectedFlagChartVariables A j))).symm

/-- Any further scalar extension of a simultaneous local presentation still
represents the original quotient step over the new coefficient ring. -/
theorem simultaneousFlagCoordinateEvaluation_step_comp
    {C : Type u} [CommRing C] [Algebra A C]
    (i : SimultaneousFlagCoordinateIndex F)
    (g : Localization.Away (simultaneousFlagCoordinateElement F i) →ₐ[A] C)
    (j : Fin (n + 1)) :
    selectedFlagChartStep A (simultaneousFlagCoordinateSelection F i)
      (g.comp (simultaneousFlagCoordinateEvaluation F i)) j =
      coordinateGrassmannianBaseChange C (F.step j) := by
  letI : Algebra (Localization.Away (simultaneousFlagCoordinateElement F i)) C := g.toAlgebra
  letI : IsScalarTower A (Localization.Away (simultaneousFlagCoordinateElement F i)) C :=
    IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  rw [selectedFlagChartStep_comp (A := A) (simultaneousFlagCoordinateSelection F i)
    (simultaneousFlagCoordinateEvaluation F i) g j,
    simultaneousFlagCoordinateEvaluation_step F i j,
    coordinateGrassmannianBaseChange_tower]

/-- The coordinate ring of the intersection of two common principal opens. -/
abbrev simultaneousFlagCoordinateOverlapRing
    (i j : SimultaneousFlagCoordinateIndex F) :=
  Localization.Away (simultaneousFlagCoordinateElement F i) ⊗[A]
    Localization.Away (simultaneousFlagCoordinateElement F j)

/-- Both local flag maps agree on their tensor-product intersection. -/
theorem simultaneousFlagLocalMap_tensor_overlap
    (i j : SimultaneousFlagCoordinateIndex F) :
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft :
        Localization.Away (simultaneousFlagCoordinateElement F i) →ₐ[A]
          simultaneousFlagCoordinateOverlapRing F i j).toRingHom) ≫
        simultaneousFlagLocalMap F i =
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight :
        Localization.Away (simultaneousFlagCoordinateElement F j) →ₐ[A]
          simultaneousFlagCoordinateOverlapRing F i j).toRingHom) ≫
        simultaneousFlagLocalMap F j := by
  let g : Localization.Away (simultaneousFlagCoordinateElement F i) →ₐ[A]
      simultaneousFlagCoordinateOverlapRing F i j := Algebra.TensorProduct.includeLeft
  let h : Localization.Away (simultaneousFlagCoordinateElement F j) →ₐ[A]
      simultaneousFlagCoordinateOverlapRing F i j := Algebra.TensorProduct.includeRight
  change Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      selectedFlagChartPointMap A (simultaneousFlagCoordinateSelection F i)
        (simultaneousFlagCoordinateEvaluation F i)
        (simultaneousFlagCoordinateEvaluation_ideal F i) =
    Spec.map (CommRingCat.ofHom h.toRingHom) ≫
      selectedFlagChartPointMap A (simultaneousFlagCoordinateSelection F j)
        (simultaneousFlagCoordinateEvaluation F j)
        (simultaneousFlagCoordinateEvaluation_ideal F j)
  rw [selectedFlagChartPointMap_comp, selectedFlagChartPointMap_comp]
  apply selectedFlagChartPointMap_eq_of_steps_eq
  intro k
  rw [simultaneousFlagCoordinateEvaluation_step_comp F i g k,
    simultaneousFlagCoordinateEvaluation_step_comp F j h k]

/-- Compatibility on the categorical pullback of two cover members. -/
theorem simultaneousFlagLocalMap_overlap
    (i j : SimultaneousFlagCoordinateIndex F) :
    pullback.fst (simultaneousFlagCoordinateSchemeCover F |>.f i)
      (simultaneousFlagCoordinateSchemeCover F |>.f j) ≫
        simultaneousFlagLocalMap F i =
    pullback.snd (simultaneousFlagCoordinateSchemeCover F |>.f i)
      (simultaneousFlagCoordinateSchemeCover F |>.f j) ≫
        simultaneousFlagLocalMap F j := by
  change pullback.fst
      (Spec.map (CommRingCat.ofHom
        (algebraMap A (Localization.Away (simultaneousFlagCoordinateElement F i)))))
      (Spec.map (CommRingCat.ofHom
        (algebraMap A (Localization.Away (simultaneousFlagCoordinateElement F j))))) ≫
        simultaneousFlagLocalMap F i =
    pullback.snd
      (Spec.map (CommRingCat.ofHom
        (algebraMap A (Localization.Away (simultaneousFlagCoordinateElement F i)))))
      (Spec.map (CommRingCat.ofHom
        (algebraMap A (Localization.Away (simultaneousFlagCoordinateElement F j))))) ≫
        simultaneousFlagLocalMap F j
  apply (cancel_epi (pullbackSpecIso A
    (Localization.Away (simultaneousFlagCoordinateElement F i))
    (Localization.Away (simultaneousFlagCoordinateElement F j))).inv).mp
  rw [← Category.assoc, ← Category.assoc,
    pullbackSpecIso_inv_fst, pullbackSpecIso_inv_snd]
  exact simultaneousFlagLocalMap_tensor_overlap F i j

end FlagVarieties.Foundations.QuotientCharts
