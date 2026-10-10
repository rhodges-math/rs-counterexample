import RSCounterexample.FlagVarieties.Foundations.Schemes.SimultaneousFlagCoordinateRelative
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedFlagGlobalFaithfulness

/-! # Overlap descent for relative flag points -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct

universe u

variable (R : Type u) [CommRing R] {A : Type u} [CommRing A]
  [Algebra R A] {n : ℕ}
  (F : RingFlag A (Fin n → A) n)

/-- Under any scalar extension of a common principal open, the local flag
point's `j`-th projection remains the intrinsic morphism of the original
step after direct coordinate base change. -/
theorem simultaneousFlagRelativeLocalMap_step_comp
    {C : Type u} [CommRing C] [Algebra A C] [Algebra R C] [IsScalarTower R A C]
    (i : SimultaneousFlagCoordinateIndex F)
    (g : Localization.Away (simultaneousFlagCoordinateElement F i) →ₐ[A] C)
    (j : Fin (n + 1)) :
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫
        simultaneousFlagRelativeLocalMap R F i ≫ selectedFlagChartSchemeStep R n j =
      selectedQuotientMorphism R (coordinateGrassmannianBaseChange C (F.step j)) := by
  letI : Algebra (Localization.Away (simultaneousFlagCoordinateElement F i)) C := g.toAlgebra
  letI : IsScalarTower A (Localization.Away (simultaneousFlagCoordinateElement F i)) C :=
    IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  calc
    _ = Spec.map (CommRingCat.ofHom g.toRingHom) ≫
        (simultaneousFlagRelativeLocalMap R F i ≫ selectedFlagChartSchemeStep R n j) :=
      Category.assoc _ _ _
    _ = Spec.map (CommRingCat.ofHom g.toRingHom) ≫
        selectedQuotientMorphism R
          (coordinateGrassmannianBaseChange
            (Localization.Away (simultaneousFlagCoordinateElement F i)) (F.step j)) :=
      congrArg (fun m => Spec.map (CommRingCat.ofHom g.toRingHom) ≫ m)
        (simultaneousFlagRelativeLocalMap_step R F i j)
    _ = selectedQuotientMorphism R
        (coordinateGrassmannianBaseChange C
          (coordinateGrassmannianBaseChange
            (Localization.Away (simultaneousFlagCoordinateElement F i)) (F.step j))) :=
      selectedQuotientMorphism_naturality (g.restrictScalars R) _
    _ = selectedQuotientMorphism R (coordinateGrassmannianBaseChange C (F.step j)) := by
      rw [coordinateGrassmannianBaseChange_tower]

/-- Two relative local maps agree over their tensor intersection. -/
theorem simultaneousFlagRelativeLocalMap_tensor_overlap
    (i j : SimultaneousFlagCoordinateIndex F) :
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft :
        Localization.Away (simultaneousFlagCoordinateElement F i) →ₐ[A]
          simultaneousFlagCoordinateOverlapRing F i j).toRingHom) ≫
        simultaneousFlagRelativeLocalMap R F i =
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight :
        Localization.Away (simultaneousFlagCoordinateElement F j) →ₐ[A]
          simultaneousFlagCoordinateOverlapRing F i j).toRingHom) ≫
        simultaneousFlagRelativeLocalMap R F j := by
  let T := simultaneousFlagCoordinateOverlapRing F i j
  let g : Localization.Away (simultaneousFlagCoordinateElement F i) →ₐ[A] T :=
    Algebra.TensorProduct.includeLeft
  let h : Localization.Away (simultaneousFlagCoordinateElement F j) →ₐ[A] T :=
    Algebra.TensorProduct.includeRight
  change Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      simultaneousFlagRelativeLocalMap R F i =
    Spec.map (CommRingCat.ofHom h.toRingHom) ≫
      simultaneousFlagRelativeLocalMap R F j
  apply selectedFlagMorphism_eq_of_projections_eq R
  intro k
  exact (simultaneousFlagRelativeLocalMap_step_comp R F i g k).trans
    (simultaneousFlagRelativeLocalMap_step_comp R F j h k).symm

/-- The relative local maps agree on the categorical cover overlap. -/
theorem simultaneousFlagRelativeLocalMap_overlap
    (i j : SimultaneousFlagCoordinateIndex F) :
    pullback.fst (simultaneousFlagCoordinateSchemeCover F |>.f i)
      (simultaneousFlagCoordinateSchemeCover F |>.f j) ≫
        simultaneousFlagRelativeLocalMap R F i =
    pullback.snd (simultaneousFlagCoordinateSchemeCover F |>.f i)
      (simultaneousFlagCoordinateSchemeCover F |>.f j) ≫
        simultaneousFlagRelativeLocalMap R F j := by
  change pullback.fst
      (Spec.map (CommRingCat.ofHom
        (algebraMap A (Localization.Away (simultaneousFlagCoordinateElement F i)))))
      (Spec.map (CommRingCat.ofHom
        (algebraMap A (Localization.Away (simultaneousFlagCoordinateElement F j))))) ≫
        simultaneousFlagRelativeLocalMap R F i =
    pullback.snd
      (Spec.map (CommRingCat.ofHom
        (algebraMap A (Localization.Away (simultaneousFlagCoordinateElement F i)))))
      (Spec.map (CommRingCat.ofHom
        (algebraMap A (Localization.Away (simultaneousFlagCoordinateElement F j))))) ≫
        simultaneousFlagRelativeLocalMap R F j
  apply (cancel_epi (pullbackSpecIso A
    (Localization.Away (simultaneousFlagCoordinateElement F i))
    (Localization.Away (simultaneousFlagCoordinateElement F j))).inv).mp
  rw [← Category.assoc, ← Category.assoc,
    pullbackSpecIso_inv_fst, pullbackSpecIso_inv_snd]
  exact simultaneousFlagRelativeLocalMap_tensor_overlap R F i j

end FlagVarieties.Foundations.QuotientCharts
