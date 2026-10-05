import Schubert.FlagVarieties.Foundations.Schemes.GeneralLinearFlagLawsGroup
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-!
# Module-object laws of the general-linear action on the flag scheme

The foundations prove the unit and multiplication laws of the varying action
`GLₙ ×_R Flₙ ⟶ Flₙ` as equalities of scheme morphisms
(`generalLinearFlagAction_unit`, `generalLinearFlagAction_mul`). This file packages them as a
Mathlib `ModObj` instance for Tau Ceti's general-linear group object in the cartesian monoidal
slice category over `Spec R`, for every commutative ring `R` and every `n`.

The proof works directly with the flag action: it identifies the categorical products of the
slice category with the coordinate products used in the foundations, and needs no auxiliary
action on other incidence schemes.

These are internal lemmas; the public interface is `Schubert.FlagVarieties.Flag.Action`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonObj MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct

universe u

/-! ### The two projections of the tensor presentation of `GLₙ × GLₙ` -/

private theorem tensorSpecIso_inv_fst_naturality
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) :
    (Scheme.Spec.mapIso
        (Algebra.TensorProduct.congr e e).toRingEquiv.toCommRingCatIso.op).inv ≫
      (pullbackSpecIso R B B).inv ≫
        pullback.fst
          (Spec.map (CommRingCat.ofHom (algebraMap R B)))
          (Spec.map (CommRingCat.ofHom (algebraMap R B))) =
    Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] A))) ≫
      (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op).inv := by
  rw [pullbackSpecIso_inv_fst']
  simp only [Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map,
    Quiver.Hom.unop_op, RingEquiv.toCommRingCatIso_inv,
    ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro b
  simp [Algebra.TensorProduct.congr_symm_apply]

private theorem tensorSpecIso_inv_snd_naturality
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) :
    (Scheme.Spec.mapIso
        (Algebra.TensorProduct.congr e e).toRingEquiv.toCommRingCatIso.op).inv ≫
      (pullbackSpecIso R B B).inv ≫
        pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap R B)))
          (Spec.map (CommRingCat.ofHom (algebraMap R B))) =
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight.toRingHom : A →+* A ⊗[R] A)) ≫
      (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op).inv := by
  rw [pullbackSpecIso_inv_snd]
  simp only [Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map,
    Quiver.Hom.unop_op, RingEquiv.toCommRingCatIso_inv,
    ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro b
  simp [Algebra.TensorProduct.congr_symm_apply]

variable (R : Type u) [CommRing R] (n : ℕ)

private theorem groupScheme_X_hom_hopf :
    (TauCeti.GeneralLinear.groupScheme R n).X.hom =
      eqToHom (TauCeti.GeneralLinear.groupScheme_X_left R n) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap R (TauCeti.GeneralLinear.coordinateHopfAlgebra R n))) := by
  unfold TauCeti.GeneralLinear.groupScheme
  convert TauCeti.hopfSpec_obj_X_hom R
    (TauCeti.GeneralLinear.coordinateHopfAlgebra R n) using 1

theorem glTensorProjection_fst :
    (TauCeti.GeneralLinear.groupSchemeMulSourceIso R n).inv ≫
      pullback.fst (TauCeti.GeneralLinear.groupScheme R n).X.hom
        (TauCeti.GeneralLinear.groupScheme R n).X.hom =
    Spec.map (CommRingCat.ofHom
      (algebraMap (TauCeti.GeneralLinear.CoordinateRing R n)
        ((TauCeti.GeneralLinear.CoordinateRing R n) ⊗[R]
          (TauCeti.GeneralLinear.CoordinateRing R n)))) ≫
      (TauCeti.GeneralLinear.groupSchemeSpecIso R n).inv := by
  unfold TauCeti.GeneralLinear.groupSchemeMulSourceIso
    TauCeti.GeneralLinear.groupSchemeSpecIso
  simp only [Iso.trans_inv, Category.assoc]
  have hGL := TauCeti.GeneralLinear.groupScheme_X_left R n
  cases hGL
  have hHom : (TauCeti.GeneralLinear.groupScheme R n).X.hom =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (TauCeti.GeneralLinear.coordinateHopfAlgebra R n))) := by
    simpa only [eqToHom_refl, Category.id_comp] using
      groupScheme_X_hom_hopf R n
  cases hHom
  simp only [eqToIso.inv, eqToHom_refl, Category.id_comp]
  exact tensorSpecIso_inv_fst_naturality R
    (TauCeti.GeneralLinear.CoordinateRing R n)
    (TauCeti.GeneralLinear.coordinateHopfAlgebra R n)
    (TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv R n)

theorem glTensorProjection_snd :
    (TauCeti.GeneralLinear.groupSchemeMulSourceIso R n).inv ≫
      pullback.snd (TauCeti.GeneralLinear.groupScheme R n).X.hom
        (TauCeti.GeneralLinear.groupScheme R n).X.hom =
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight.toRingHom :
        TauCeti.GeneralLinear.CoordinateRing R n →+*
          (TauCeti.GeneralLinear.CoordinateRing R n) ⊗[R]
            (TauCeti.GeneralLinear.CoordinateRing R n))) ≫
      (TauCeti.GeneralLinear.groupSchemeSpecIso R n).inv := by
  unfold TauCeti.GeneralLinear.groupSchemeMulSourceIso
    TauCeti.GeneralLinear.groupSchemeSpecIso
  simp only [Iso.trans_inv, Category.assoc]
  have hGL := TauCeti.GeneralLinear.groupScheme_X_left R n
  cases hGL
  have hHom : (TauCeti.GeneralLinear.groupScheme R n).X.hom =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (TauCeti.GeneralLinear.coordinateHopfAlgebra R n))) := by
    simpa only [eqToHom_refl, Category.id_comp] using
      groupScheme_X_hom_hopf R n
  cases hHom
  simp only [eqToIso.inv, eqToHom_refl, Category.id_comp]
  exact tensorSpecIso_inv_snd_naturality R
    (TauCeti.GeneralLinear.CoordinateRing R n)
    (TauCeti.GeneralLinear.coordinateHopfAlgebra R n)
    (TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv R n)

/-! ### The coordinate pair of group elements is the categorical pair -/

theorem generalLinearFlagGroupPair_fst :
    generalLinearFlagGroupPair R n ≫
      pullback.fst (TauCeti.GeneralLinear.groupScheme R n).X.hom
        (TauCeti.GeneralLinear.groupScheme R n).X.hom =
    generalLinearFlagOuterCoordinate R n ≫
      (TauCeti.GeneralLinear.groupSchemeSpecIso R n).inv := by
  unfold generalLinearFlagGroupPair generalLinearFlagTensorCoordinates
  simp only [Category.assoc, glTensorProjection_fst]
  conv_lhs => rhs; rw [← Category.assoc, pullbackSpecIso_hom_fst']
  rw [← Category.assoc, generalLinearFlagCoordinatePair_outer]

theorem generalLinearFlagGroupPair_snd :
    generalLinearFlagGroupPair R n ≫
      pullback.snd (TauCeti.GeneralLinear.groupScheme R n).X.hom
        (TauCeti.GeneralLinear.groupScheme R n).X.hom =
    generalLinearFlagInnerProduct R n ≫ generalLinearFlagGroup R n := by
  unfold generalLinearFlagGroupPair generalLinearFlagTensorCoordinates
  simp only [Category.assoc, glTensorProjection_snd]
  have hs : (pullbackSpecIso R
        (TauCeti.GeneralLinear.CoordinateRing R n)
        (TauCeti.GeneralLinear.CoordinateRing R n)).hom ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight.toRingHom :
          TauCeti.GeneralLinear.CoordinateRing R n →+*
            (TauCeti.GeneralLinear.CoordinateRing R n) ⊗[R]
              (TauCeti.GeneralLinear.CoordinateRing R n))) =
      pullback.snd _ _ := pullbackSpecIso_hom_snd _ _ _
  conv_lhs => rhs; rw [← Category.assoc, hs]
  rw [← Category.assoc, generalLinearFlagCoordinatePair_inner]
  unfold generalLinearFlagCoordinateMap
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

@[reassoc] theorem generalLinearFlagMultipliedPoint_group_mul :
    generalLinearFlagMultipliedPoint R n ≫ generalLinearFlagGroup R n =
      generalLinearFlagGroupPair R n ≫
        μ[(TauCeti.GeneralLinear.groupScheme R n).X].left := by
  rw [generalLinearFlagMultipliedPoint_group, generalLinearFlagGroupPair_mul]

/-! ### The action as a morphism of the slice category

The monoidal structure on `Over (Spec R)` is Mathlib's cartesian one
(`AlgebraicGeometry.instCartesianMonoidalCategoryOver`), as for Tau Ceti's group schemes. -/

/-- The flag scheme as an object of the slice category over `Spec R`. -/
abbrev generalLinearFlagOver : Over (Spec (CommRingCat.of R)) :=
  Over.mk (selectedFlagChartSchemeToSpec R n)

private abbrev G : Over (Spec (CommRingCat.of R)) :=
  (TauCeti.GeneralLinear.groupScheme R n).X

private abbrev X : Over (Spec (CommRingCat.of R)) :=
  generalLinearFlagOver R n

/-- The varying action, as a morphism `GLₙ ⊗ Flₙ ⟶ Flₙ` of the slice category. -/
def generalLinearFlagOverAction : G R n ⊗ X R n ⟶ X R n :=
  Over.homMk (generalLinearFlagAction R n) (by
    change generalLinearFlagAction R n ≫ selectedFlagChartSchemeToSpec R n =
      pullback.fst _ _ ≫ (TauCeti.GeneralLinear.groupScheme R n).X.hom
    rw [generalLinearFlagAction_toSpec]
    exact pullback.condition.symm)

theorem generalLinearFlagOverAction_left :
    (generalLinearFlagOverAction R n).left = generalLinearFlagAction R n := rfl

/-! ### The unit law -/

private theorem generalLinearGroupPoint_unit_eq_one :
    generalLinearGroupPoint R R n (generalLinearUnitAlgebraPoint R R n) =
      η[(TauCeti.GeneralLinear.groupScheme R n).X].left := by
  rw [TauCeti.GeneralLinear.groupScheme_one_left]
  unfold generalLinearGroupPoint generalLinearUnitAlgebraPoint
  congr 1

/-- The categorical insertion of the unit into `G × X` is the unit section of the foundations,
after the left unitor. -/
theorem generalLinearFlagOverAction_unit_input :
    (η[G R n] ▷ X R n).left =
      (λ_ (X R n)).hom.left ≫ generalLinearFlagUnitSection R n := by
  apply pullback.hom_ext
  · change (η[G R n] ▷ X R n).left ≫
        pullback.fst (TauCeti.GeneralLinear.groupScheme R n).X.hom
          (selectedFlagChartSchemeToSpec R n) =
      ((λ_ (X R n)).hom.left ≫ generalLinearFlagUnitSection R n) ≫
        pullback.fst (TauCeti.GeneralLinear.groupScheme R n).X.hom
          (selectedFlagChartSchemeToSpec R n)
    simp only [generalLinearFlagUnitSection, generalLinearFlagProduct,
      pullback.lift_fst, Category.assoc,
      generalLinearGroupPoint_unit_eq_one, Over.leftUnitor_hom_left]
    have hw := Over.whiskerRight_left_fst (R := X R n) (η[G R n])
    change (η[G R n] ▷ X R n).left ≫
        pullback.fst (TauCeti.GeneralLinear.groupScheme R n).X.hom
          (selectedFlagChartSchemeToSpec R n) =
      pullback.fst (𝟙_ (Over (Spec (CommRingCat.of R)))).hom
        (selectedFlagChartSchemeToSpec R n) ≫ η[G R n].left at hw
    calc
      _ = pullback.fst (𝟙_ (Over (Spec (CommRingCat.of R)))).hom
          (selectedFlagChartSchemeToSpec R n) ≫ η[G R n].left := by
            simpa only [X, G] using hw
      _ = _ := by
        change pullback.fst (𝟙 (Spec (CommRingCat.of R)))
            (selectedFlagChartSchemeToSpec R n) ≫ η[G R n].left =
          (pullback.snd (𝟙 (Spec (CommRingCat.of R)))
            (selectedFlagChartSchemeToSpec R n) ≫ selectedFlagChartSchemeToSpec R n) ≫
              η[G R n].left
        have hc : pullback.fst (𝟙 (Spec (CommRingCat.of R)))
            (selectedFlagChartSchemeToSpec R n) =
          pullback.snd (𝟙 (Spec (CommRingCat.of R)))
            (selectedFlagChartSchemeToSpec R n) ≫ selectedFlagChartSchemeToSpec R n := by
          simpa only [Category.comp_id] using
            (pullback.condition (f := 𝟙 (Spec (CommRingCat.of R)))
              (g := selectedFlagChartSchemeToSpec R n))
        exact congrArg (fun h => h ≫ η[G R n].left) hc
  · change (η[G R n] ▷ X R n).left ≫
        pullback.snd (TauCeti.GeneralLinear.groupScheme R n).X.hom
          (selectedFlagChartSchemeToSpec R n) =
      ((λ_ (X R n)).hom.left ≫ generalLinearFlagUnitSection R n) ≫
        pullback.snd (TauCeti.GeneralLinear.groupScheme R n).X.hom
          (selectedFlagChartSchemeToSpec R n)
    simp only [generalLinearFlagUnitSection, generalLinearFlagProduct,
      pullback.lift_snd, Category.assoc, Over.leftUnitor_hom_left]
    have hw := Over.whiskerRight_left_snd (R := X R n) (η[G R n])
    change (η[G R n] ▷ X R n).left ≫
        pullback.snd (TauCeti.GeneralLinear.groupScheme R n).X.hom
          (selectedFlagChartSchemeToSpec R n) =
      pullback.snd (𝟙_ (Over (Spec (CommRingCat.of R)))).hom
        (selectedFlagChartSchemeToSpec R n) at hw
    calc
      _ = pullback.snd (𝟙_ (Over (Spec (CommRingCat.of R)))).hom
          (selectedFlagChartSchemeToSpec R n) := by
            simpa only [X, G] using hw
      _ = _ := by simp

/-- The unit acts trivially, as a morphism of the slice category. -/
theorem generalLinearFlagOverAction_one :
    η[G R n] ▷ X R n ≫ generalLinearFlagOverAction R n = (λ_ (X R n)).hom := by
  apply Over.OverMorphism.ext
  change (η[G R n] ▷ X R n).left ≫ generalLinearFlagAction R n = (λ_ (X R n)).hom.left
  rw [generalLinearFlagOverAction_unit_input, Category.assoc, generalLinearFlagAction_unit]
  exact Category.comp_id _

/-! ### The multiplication law -/

private theorem doubleSource_inner_base :
    ((G R n ⊗ X R n).hom : (G R n ⊗ X R n).left ⟶ Spec (CommRingCat.of R)) =
      generalLinearFlagToSpec R n := by
  change pullback.fst (G R n).hom (X R n).hom ≫ (G R n).hom =
    pullback.snd (G R n).hom (X R n).hom ≫ selectedFlagChartSchemeToSpec R n
  exact pullback.condition

/-- The coordinate presentation of the outer factor identifies the iterated categorical product
`G ⊗ (G ⊗ X)` with the double product of the foundations. -/
def generalLinearFlagDoubleSourceIso :
    (G R n ⊗ (G R n ⊗ X R n)).left ≅ generalLinearFlagDoubleProduct R n := by
  have h₁ : (G R n).hom ≫ 𝟙 (Spec (CommRingCat.of R)) =
      (TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap R (TauCeti.GeneralLinear.CoordinateRing R n))) := by
    simpa only [Category.comp_id] using TauCeti.GeneralLinear.groupScheme_X_hom R n
  have h₂ : (G R n ⊗ X R n).hom ≫ 𝟙 (Spec (CommRingCat.of R)) =
      𝟙 (G R n ⊗ X R n).left ≫ generalLinearFlagToSpec R n := by
    rw [Category.comp_id, Category.id_comp]
    exact doubleSource_inner_base R n
  let m := pullback.map
    (G R n).hom (G R n ⊗ X R n).hom
    (Spec.map (CommRingCat.ofHom
      (algebraMap R (TauCeti.GeneralLinear.CoordinateRing R n))))
    (generalLinearFlagToSpec R n)
    (TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom
    (𝟙 (G R n ⊗ X R n).left) (𝟙 (Spec (CommRingCat.of R)))
    h₁ h₂
  letI : IsIso (𝟙 (G R n ⊗ X R n).left) := IsIso.id _
  letI : IsIso (𝟙 (Spec (CommRingCat.of R))) := IsIso.id _
  haveI : IsIso m := by
    dsimp [m]
    exact Limits.pullback.map_isIso _ _ _ _ _ _ _ _ _
  exact asIso m

@[reassoc] theorem generalLinearFlagDoubleSourceIso_outer :
    (generalLinearFlagDoubleSourceIso R n).hom ≫ generalLinearFlagOuterCoordinate R n =
      pullback.fst (G R n).hom (G R n ⊗ X R n).hom ≫
        (TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom := by
  simp only [generalLinearFlagDoubleSourceIso, generalLinearFlagOuterCoordinate,
    pullback.map, asIso_hom, pullback.lift_fst]

@[reassoc] theorem generalLinearFlagDoubleSourceIso_inner :
    (generalLinearFlagDoubleSourceIso R n).hom ≫ generalLinearFlagInnerProduct R n =
      pullback.snd (G R n).hom (G R n ⊗ X R n).hom := by
  simp only [generalLinearFlagDoubleSourceIso, generalLinearFlagInnerProduct,
    pullback.map, asIso_hom, pullback.lift_snd, Category.comp_id]

/-- The comparison from the left-associated categorical triple product to the double product
of the foundations. -/
def generalLinearFlagCategoricalDoubleComparison :
    ((G R n ⊗ G R n) ⊗ X R n).left ⟶ generalLinearFlagDoubleProduct R n :=
  (α_ (G R n) (G R n) (X R n)).hom.left ≫ (generalLinearFlagDoubleSourceIso R n).hom

@[reassoc] theorem generalLinearFlagCategoricalDoubleComparison_outer :
    generalLinearFlagCategoricalDoubleComparison R n ≫ generalLinearFlagOuterCoordinate R n =
      (pullback.fst (G R n ⊗ G R n).hom (X R n).hom ≫
        pullback.fst (G R n).hom (G R n).hom) ≫
        (TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom := by
  unfold generalLinearFlagCategoricalDoubleComparison
  rw [Category.assoc, generalLinearFlagDoubleSourceIso_outer, ← Category.assoc]
  exact congrArg (fun h => h ≫ (TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom)
    (Over.associator_hom_left_fst (G R n) (G R n) (X R n))

@[reassoc] theorem generalLinearFlagCategoricalDoubleComparison_inner :
    generalLinearFlagCategoricalDoubleComparison R n ≫ generalLinearFlagInnerProduct R n =
      (α_ (G R n) (G R n) (X R n)).hom.left ≫
        pullback.snd (G R n).hom (G R n ⊗ X R n).hom := by
  unfold generalLinearFlagCategoricalDoubleComparison
  rw [Category.assoc, generalLinearFlagDoubleSourceIso_inner]

@[reassoc] theorem generalLinearFlagCategoricalDoubleComparison_pair :
    generalLinearFlagCategoricalDoubleComparison R n ≫ generalLinearFlagGroupPair R n =
      pullback.fst (G R n ⊗ G R n).hom (X R n).hom := by
  apply pullback.hom_ext
  · change (generalLinearFlagCategoricalDoubleComparison R n ≫
        generalLinearFlagGroupPair R n) ≫ pullback.fst (G R n).hom (G R n).hom =
      pullback.fst (G R n ⊗ G R n).hom (X R n).hom ≫ pullback.fst (G R n).hom (G R n).hom
    rw [Category.assoc, generalLinearFlagGroupPair_fst, ← Category.assoc,
      generalLinearFlagCategoricalDoubleComparison_outer, Category.assoc]
    simp only [Iso.hom_inv_id, Category.comp_id]
  · change (generalLinearFlagCategoricalDoubleComparison R n ≫
        generalLinearFlagGroupPair R n) ≫ pullback.snd (G R n).hom (G R n).hom =
      pullback.fst (G R n ⊗ G R n).hom (X R n).hom ≫ pullback.snd (G R n).hom (G R n).hom
    rw [Category.assoc, generalLinearFlagGroupPair_snd, ← Category.assoc,
      generalLinearFlagCategoricalDoubleComparison_inner, Category.assoc]
    change (α_ (G R n) (G R n) (X R n)).hom.left ≫
        pullback.snd (G R n).hom (G R n ⊗ X R n).hom ≫
          pullback.fst (G R n).hom (X R n).hom =
      pullback.fst (G R n ⊗ G R n).hom (X R n).hom ≫ pullback.snd (G R n).hom (G R n).hom
    exact Over.associator_hom_left_snd_fst (G R n) (G R n) (X R n)

/-- The categorical multiplication insertion is the multiplied point of the foundations,
after the comparison. -/
theorem generalLinearFlagCategoricalMultipliedPoint :
    (μ[G R n] ▷ X R n).left =
      generalLinearFlagCategoricalDoubleComparison R n ≫
        generalLinearFlagMultipliedPoint R n := by
  apply pullback.hom_ext
  · change (μ[G R n] ▷ X R n).left ≫ pullback.fst (G R n).hom (X R n).hom =
      (generalLinearFlagCategoricalDoubleComparison R n ≫
        generalLinearFlagMultipliedPoint R n) ≫ generalLinearFlagGroup R n
    conv_rhs => rw [Category.assoc, generalLinearFlagMultipliedPoint_group_mul,
      ← Category.assoc, generalLinearFlagCategoricalDoubleComparison_pair]
    exact Over.whiskerRight_left_fst (R := X R n) (μ[G R n])
  · change (μ[G R n] ▷ X R n).left ≫ pullback.snd (G R n).hom (X R n).hom =
      (generalLinearFlagCategoricalDoubleComparison R n ≫
        generalLinearFlagMultipliedPoint R n) ≫ generalLinearFlagPoint R n
    conv_rhs => rw [Category.assoc, generalLinearFlagMultipliedPoint_point,
      ← Category.assoc, generalLinearFlagCategoricalDoubleComparison_inner, Category.assoc]
    rw [Over.whiskerRight_left_snd]
    exact (Over.associator_hom_left_snd_snd (G R n) (G R n) (X R n)).symm

/-- Whiskering the action by the outer factor is the successive point of the foundations. -/
theorem generalLinearFlagCategoricalSuccessivePoint :
    (G R n ◁ generalLinearFlagOverAction R n).left =
      (generalLinearFlagDoubleSourceIso R n).hom ≫ generalLinearFlagSuccessivePoint R n := by
  apply pullback.hom_ext
  · change (G R n ◁ generalLinearFlagOverAction R n).left ≫
        pullback.fst (G R n).hom (X R n).hom =
      ((generalLinearFlagDoubleSourceIso R n).hom ≫
        generalLinearFlagSuccessivePoint R n) ≫ generalLinearFlagGroup R n
    conv_rhs => rw [Category.assoc, generalLinearFlagSuccessivePoint_group,
      ← Category.assoc, generalLinearFlagDoubleSourceIso_outer, Category.assoc]
    rw [Over.whiskerLeft_left_fst]
    simp only [Iso.hom_inv_id, Category.comp_id]
  · change (G R n ◁ generalLinearFlagOverAction R n).left ≫
        pullback.snd (G R n).hom (X R n).hom =
      ((generalLinearFlagDoubleSourceIso R n).hom ≫
        generalLinearFlagSuccessivePoint R n) ≫ generalLinearFlagPoint R n
    conv_rhs => rw [Category.assoc, generalLinearFlagSuccessivePoint_point,
      ← Category.assoc, generalLinearFlagDoubleSourceIso_inner]
    exact Over.whiskerLeft_left_snd (generalLinearFlagOverAction R n)

/-- Compatibility of the action with the group multiplication, in the slice category. -/
theorem generalLinearFlagOverAction_mul :
    μ[G R n] ▷ X R n ≫ generalLinearFlagOverAction R n =
      (α_ (G R n) (G R n) (X R n)).hom ≫
        G R n ◁ generalLinearFlagOverAction R n ≫ generalLinearFlagOverAction R n := by
  apply Over.OverMorphism.ext
  change (μ[G R n] ▷ X R n).left ≫ generalLinearFlagAction R n =
    ((α_ (G R n) (G R n) (X R n)).hom.left ≫
      (G R n ◁ generalLinearFlagOverAction R n).left) ≫ generalLinearFlagAction R n
  have hmul : generalLinearFlagMultipliedPoint R n ≫ generalLinearFlagAction R n =
      generalLinearFlagSuccessivePoint R n ≫ generalLinearFlagAction R n :=
    generalLinearFlagAction_mul R n
  rw [generalLinearFlagCategoricalMultipliedPoint, Category.assoc, hmul,
    generalLinearFlagCategoricalSuccessivePoint, generalLinearFlagCategoricalDoubleComparison]
  simp only [Category.assoc]

/-- Tau Ceti's general-linear group object acts on the flag scheme, in the cartesian monoidal
slice category over `Spec R`. -/
instance instGeneralLinearFlagModObj :
    ModObj (TauCeti.GeneralLinear.groupScheme R n).X (generalLinearFlagOver R n) where
  smul := generalLinearFlagOverAction R n
  one_smul := generalLinearFlagOverAction_one R n
  mul_smul := generalLinearFlagOverAction_mul R n

theorem generalLinearFlagModObj_smul_left :
    (ModObj.smul (M := (TauCeti.GeneralLinear.groupScheme R n).X)
      (X := generalLinearFlagOver R n)).left = generalLinearFlagAction R n := rfl

end FlagVarieties.Foundations.QuotientCharts
