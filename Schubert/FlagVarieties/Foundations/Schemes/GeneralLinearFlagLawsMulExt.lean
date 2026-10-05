import Schubert.FlagVarieties.Foundations.Schemes.GeneralLinearFlagLawsMulScheme
import Schubert.FlagVarieties.Foundations.Schemes.AffinePointAlgebraHom

/-! Every affine point of the two-factor relative product is an
evaluation of the two original GL coordinate algebras and one
flag quotient. -/

noncomputable section
set_option linter.style.haveILetI false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] (n : ℕ)

private abbrev GLCoord := TauCeti.GeneralLinear.CoordinateRing R n

theorem generalLinearFlagDouble_affine_factor
    (f : Spec (CommRingCat.of B) ⟶ generalLinearFlagDoubleProduct R n)
    (hb : (f ≫ generalLinearFlagOuterCoordinate R n) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (GLCoord R n))) =
      Spec.map (CommRingCat.ofHom (algebraMap R B))) :
    ∃ (k l : GLCoord R n →ₐ[R] B)
      (P : RingFlag B (Fin n → B) n),
      f = generalLinearFlagDoubleOfAffine R n B k l P := by
  have hinnerBase : (f ≫ generalLinearFlagInnerProduct R n) ≫
      generalLinearFlagToSpec R n =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
    calc
      (f ≫ generalLinearFlagInnerProduct R n) ≫
          generalLinearFlagToSpec R n =
        f ≫ (generalLinearFlagInnerProduct R n ≫
          generalLinearFlagToSpec R n) := Category.assoc _ _ _
      _ = f ≫ (generalLinearFlagOuterCoordinate R n ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (GLCoord R n)))) := by
        rw [generalLinearFlagDouble_condition]
      _ = Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
        rw [← Category.assoc]
        exact hb
  have hinnerCoord : ((f ≫ generalLinearFlagInnerProduct R n) ≫
        generalLinearFlagCoordinateMap R n) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (GLCoord R n))) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
    rw [Category.assoc, generalLinearFlagCoordinate_toSpec]
    exact hinnerBase
  have hinnerPoint : ((f ≫ generalLinearFlagInnerProduct R n) ≫
        generalLinearFlagPoint R n) ≫
      selectedFlagChartSchemeToSpec R n =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
    rw [Category.assoc]
    exact hinnerBase
  let k := affinePointAlgebraHom R
    (f ≫ generalLinearFlagOuterCoordinate R n) hb
  let l := affinePointAlgebraHom R
    ((f ≫ generalLinearFlagInnerProduct R n) ≫
      generalLinearFlagCoordinateMap R n) hinnerCoord
  let P := selectedFlagRingOfAffine R (CommRingCat.of B) n
    ⟨((f ≫ generalLinearFlagInnerProduct R n) ≫
      generalLinearFlagPoint R n), hinnerPoint⟩
  refine ⟨k, l, P, ?_⟩
  apply pullback.hom_ext
  · change f ≫ generalLinearFlagOuterCoordinate R n =
      generalLinearFlagDoubleOfAffine R n B k l P ≫
        generalLinearFlagOuterCoordinate R n
    rw [generalLinearFlagDoubleOfAffine_outer]
    exact (affinePointAlgebraHom_spec R _ hb).symm
  · change f ≫ generalLinearFlagInnerProduct R n =
      generalLinearFlagDoubleOfAffine R n B k l P ≫
        generalLinearFlagInnerProduct R n
    rw [generalLinearFlagDoubleOfAffine_inner]
    apply pullback.hom_ext
    · change (f ≫ generalLinearFlagInnerProduct R n) ≫
          generalLinearFlagGroup R n =
        generalLinearFlagOfAffine R B n l P ≫
          generalLinearFlagGroup R n
      apply (cancel_mono (TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom).mp
      rw [Category.assoc, generalLinearFlagOfAffine_group]
      unfold generalLinearGroupPoint
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact (affinePointAlgebraHom_spec R _ hinnerCoord).symm
    · change (f ≫ generalLinearFlagInnerProduct R n) ≫
          generalLinearFlagPoint R n =
        generalLinearFlagOfAffine R B n l P ≫
          generalLinearFlagPoint R n
      rw [generalLinearFlagOfAffine_point]
      exact (congrArg Subtype.val
        (selectedFlagAffineOfRing_ringOfAffine R (CommRingCat.of B) n
          ⟨((f ≫ generalLinearFlagInnerProduct R n) ≫
            generalLinearFlagPoint R n), hinnerPoint⟩)).symm

/-- The raw Hopf multiplication of two varying matrices acts in the same
order as two successive actions. This is equality of morphisms from the
relative three-factor scheme, not an equality merely on field points. -/
theorem generalLinearFlagAction_mul :
    generalLinearFlagMultipliedAction R n =
      generalLinearFlagSuccessiveAction R n := by
  let C := (generalLinearFlagDoubleProduct R n).affineOpenCover
  apply C.openCover.hom_ext
  intro i
  let j := C.f i
  let A := C.X i
  let b : Spec A ⟶ Spec (CommRingCat.of R) :=
    (j ≫ generalLinearFlagOuterCoordinate R n) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (GLCoord R n)))
  letI : Algebra R A := (Spec.fullyFaithful.preimage b).unop.hom.toAlgebra
  have hb : (j ≫ generalLinearFlagOuterCoordinate R n) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (GLCoord R n))) =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    change b = Spec.map (Spec.fullyFaithful.preimage b).unop
    exact (Spec.map_preimage_unop b).symm
  obtain ⟨k, l, P, hj⟩ :=
    @generalLinearFlagDouble_affine_factor R A _ _
      ((Spec.fullyFaithful.preimage b).unop.hom.toAlgebra) n j hb
  calc
    j ≫ generalLinearFlagMultipliedAction R n =
      generalLinearFlagDoubleOfAffine R n A k l P ≫
        generalLinearFlagMultipliedAction R n := by rw [hj]
    _ = generalLinearFlagDoubleOfAffine R n A k l P ≫
        generalLinearFlagSuccessiveAction R n :=
      generalLinearFlagAction_mul_affine_test R n A k l P
    _ = j ≫ generalLinearFlagSuccessiveAction R n := by rw [hj]

end FlagVarieties.Foundations.QuotientCharts

