import Schubert.FlagVarieties.Foundations.Schemes.GeneralLinearFlagAffine
import Schubert.FlagVarieties.Foundations.Schemes.GlobalQuotientFlagAffineComparison
import Schubert.FlagVarieties.Foundations.Schemes.SelectedFlagAffineUniversalRecovery
import Schubert.FlagVarieties.Foundations.Flags.RingTransport

/-! The varying matrix acts on every original affine ring flag. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory ModuleSheafGluing
universe u

private theorem affineKernel_targetIso_flag
    (B : CommRingCat.{u}) {n : ℕ} {M N : (Spec B).Modules}
    (q : coordinateFreeSheaf (Spec B) n ⟶ M) (e : M ≅ N) :
    LinearMap.ker (affineCoordinateQuotientMap B (q ≫ e.hom)) =
      LinearMap.ker (affineCoordinateQuotientMap B q) := by
  have hm : affineCoordinateQuotientMap B (q ≫ e.hom) =
      (moduleSpecΓFunctor.map e.hom).hom.comp (affineCoordinateQuotientMap B q) := by
    apply LinearMap.ext
    intro x
    change (moduleSpecΓFunctor.map (q ≫ e.hom)).hom
      ((coordinateFreeGlobalIso B n).hom.hom x) = _
    rw [Functor.map_comp]
    rfl
  rw [hm]
  apply Submodule.ext
  intro x
  have hi : Function.Injective (moduleSpecΓFunctor.map e.hom).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  simp only [LinearMap.mem_ker, LinearMap.comp_apply]
  constructor
  · intro hx
    apply hi
    simpa only [map_zero] using hx
  · intro hx
    rw [hx, map_zero]

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
  (n : ℕ) (k : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] B)
  (P : RingFlag B (Fin n → B) n)

private def generalLinearFlagAffineStepIso (j : Fin (n+1)) :
    (Scheme.Modules.pullback (generalLinearFlagOfAffine R B n k P)).obj
      ((generalLinearFlagFamily R n).target j) ≅
      coordinateQuotientSheaf (CommRingCat.of B) (P.step j) :=
  generalLinearFlagAffineTargetIso R B n k P j ≪≫
    selectedFlagAffineStepIso R (CommRingCat.of B) P
      (simultaneousFlagRelativeMorphism R P)
      (simultaneousFlagRelativeMorphism_step R P) j

private theorem generalLinearFlagAffineStepIso_source (j : Fin (n+1)) :
    ((generalLinearFlagFamily R n).pullback
      (generalLinearFlagOfAffine R B n k P)).quotient j ≫
      (generalLinearFlagAffineStepIso R B n k P j).hom =
    (constantMatrixSpecIso (CommRingCat.of B)
      (generalLinearMatrixAt R B n k)
      (generalLinearMatrixAt_isUnit R B n k)).inv ≫
      coordinateQuotientSheafMap (CommRingCat.of B) (P.step j) := by
  unfold generalLinearFlagAffineStepIso
  simp only [QuotientFlagFamily.pullback_quotient, Iso.trans_hom]
  rw [← Category.assoc, generalLinearFlagAffineQuotient_source]
  rw [Category.assoc, selectedFlagAffineStepIso_source]

/-- The pulled-back quotient chain recovers the matrix
transport of every original affine flag kernel. -/
theorem generalLinearFlagFamily_affine_toRingFlag :
    (((generalLinearFlagFamily R n).pullback
      (generalLinearFlagOfAffine R B n k P)).toRingFlag (CommRingCat.of B)) =
    RingFlag.transport P
      ((generalLinearMatrixAt R B n k).toLinearEquiv'
        (generalLinearMatrixAt_isUnit R B n k).invertible) := by
  apply RingFlag.ext
  intro j
  rw [RingFlag.transport_step]
  let F := (generalLinearFlagFamily R n).pullback
    (generalLinearFlagOfAffine R B n k P)
  let q := F.quotient j
  let e := generalLinearFlagAffineStepIso R B n k P j
  change LinearMap.ker (affineCoordinateQuotientMap (CommRingCat.of B) q) =
    Submodule.map
      ((generalLinearMatrixAt R B n k).toLinearEquiv'
        (generalLinearMatrixAt_isUnit R B n k).invertible).toLinearMap
      (P.step j).toSubmodule
  rw [← affineKernel_targetIso_flag (CommRingCat.of B) q e,
    generalLinearFlagAffineStepIso_source,
    affineCoordinateQuotientMap_constantMatrix_inv_ker,
    affineCoordinateQuotientMap_ker_of_coordinate]

/-- Evaluation of the varying action is equality of
`Spec B → Flag_R` scheme morphisms. -/
theorem generalLinearFlagAction_evaluate :
    generalLinearFlagOfAffine R B n k P ≫ generalLinearFlagAction R n =
      simultaneousFlagRelativeMorphism R
        (RingFlag.transport P
          ((generalLinearMatrixAt R B n k).toLinearEquiv'
            (generalLinearMatrixAt_isUnit R B n k).invertible)) := by
  let f := generalLinearFlagOfAffine R B n k P
  have hb : f ≫ generalLinearFlagToSpec R n =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
    change (f ≫ generalLinearFlagPoint R n) ≫ selectedFlagChartSchemeToSpec R n = _
    rw [generalLinearFlagOfAffine_point]
    exact simultaneousFlagRelativeMorphism_toSpec R P
  change f ≫ globalQuotientFlagMorphism R
    (generalLinearFlagToSpec R n) (generalLinearFlagFamily R n) = _
  rw [globalQuotientFlagMorphism_pullback]
  rw [hb]
  rw [globalQuotientFlagMorphism_affine R (CommRingCat.of B)
    ((generalLinearFlagFamily R n).pullback f),
    generalLinearFlagFamily_affine_toRingFlag]

end FlagVarieties.Foundations.QuotientCharts
