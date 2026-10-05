import Schubert.FlagVarieties.Foundations.Schemes.SimultaneousFlagCoordinateRelativeGlue

/-!
# Relative global classifying map of an affine ring flag

For every coefficient algebra `R → A`, the flag over `A` supplies a
morphism from `Spec A` to the glued flag scheme over `R`. Its quotient
projections and coefficient-base map are the original ones.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory

universe u

variable (R : Type u) [CommRing R] {A : Type u} [CommRing A]
  [Algebra R A] {n : ℕ}
  (F : RingFlag A (Fin n → A) n)

/-- The global map obtained by gluing the relative flag points over
the simultaneous derived principal cover. -/
def simultaneousFlagRelativeMorphism :
    Spec (CommRingCat.of A) ⟶ selectedFlagChartScheme R n :=
  (simultaneousFlagCoordinateSchemeCover F).glueMorphisms
    (simultaneousFlagRelativeLocalMap R F)
    (simultaneousFlagRelativeLocalMap_overlap R F)

@[reassoc] theorem simultaneousFlagRelativeMorphism_local
    (i : SimultaneousFlagCoordinateIndex F) :
    (simultaneousFlagCoordinateSchemeCover F).f i ≫
      simultaneousFlagRelativeMorphism R F =
        simultaneousFlagRelativeLocalMap R F i :=
  (simultaneousFlagCoordinateSchemeCover F).ι_glueMorphisms
    (simultaneousFlagRelativeLocalMap R F)
    (simultaneousFlagRelativeLocalMap_overlap R F) i

/-- Every global projection is the intrinsic `R`-relative classifying map
of the original quotient step over `A`. -/
@[reassoc] theorem simultaneousFlagRelativeMorphism_step (j : Fin (n + 1)) :
    simultaneousFlagRelativeMorphism R F ≫ selectedFlagChartSchemeStep R n j =
      selectedQuotientMorphism R (F.step j) := by
  apply (simultaneousFlagCoordinateSchemeCover F).hom_ext
  intro i
  calc
    (simultaneousFlagCoordinateSchemeCover F).f i ≫
        (simultaneousFlagRelativeMorphism R F ≫ selectedFlagChartSchemeStep R n j) =
      simultaneousFlagRelativeLocalMap R F i ≫ selectedFlagChartSchemeStep R n j := by
        exact (Category.assoc _ _ _).symm.trans
          (congrArg (fun m => m ≫ selectedFlagChartSchemeStep R n j)
            (simultaneousFlagRelativeMorphism_local R F i))
    _ = selectedQuotientMorphism R
        (coordinateGrassmannianBaseChange
          (Localization.Away (simultaneousFlagCoordinateElement F i)) (F.step j)) :=
      simultaneousFlagRelativeLocalMap_step R F i j
    _ = (simultaneousFlagCoordinateSchemeCover F).f i ≫
        selectedQuotientMorphism R (F.step j) :=
      (selectedQuotientMorphism_baseChange (F.step j)).symm

/-- Its coefficient-base composite is the map `Spec A → Spec R`. -/
@[reassoc] theorem simultaneousFlagRelativeMorphism_toSpec :
    simultaneousFlagRelativeMorphism R F ≫ selectedFlagChartSchemeToSpec R n =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  apply (simultaneousFlagCoordinateSchemeCover F).hom_ext
  intro i
  calc
    (simultaneousFlagCoordinateSchemeCover F).f i ≫
        (simultaneousFlagRelativeMorphism R F ≫ selectedFlagChartSchemeToSpec R n) =
      simultaneousFlagRelativeLocalMap R F i ≫ selectedFlagChartSchemeToSpec R n := by
        exact (Category.assoc _ _ _).symm.trans
          (congrArg (fun m => m ≫ selectedFlagChartSchemeToSpec R n)
            (simultaneousFlagRelativeMorphism_local R F i))
    _ = Spec.map (CommRingCat.ofHom
        (algebraMap R (Localization.Away (simultaneousFlagCoordinateElement F i)))) :=
      simultaneousFlagRelativeLocalMap_toSpec R F i
    _ = (simultaneousFlagCoordinateSchemeCover F).f i ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
      exact (spec_map_algHom_toSpec R
        (IsScalarTower.toAlgHom R A
          (Localization.Away (simultaneousFlagCoordinateElement F i)))).symm

end FlagVarieties.Foundations.QuotientCharts
