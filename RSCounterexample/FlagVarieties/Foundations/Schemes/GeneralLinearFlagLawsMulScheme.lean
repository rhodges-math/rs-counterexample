import RSCounterexample.FlagVarieties.Foundations.Schemes.GeneralLinearFlagLawsAffine

/-! Two general-linear factors over the original coefficient base.
The raw Hopf coordinate multiplication below will be compared with the
successive varying action as scheme morphisms. -/

noncomputable section
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ)

private abbrev GLCoord := TauCeti.GeneralLinear.CoordinateRing R n

/-- The product `GLₙ ×_R (GLₙ ×_R Flₙ)`, with the outer factor written as `Spec 𝒪(GLₙ)`. -/
def generalLinearFlagDoubleProduct : Scheme.{u} :=
  pullback (Spec.map (CommRingCat.ofHom (algebraMap R (GLCoord R n))))
    (generalLinearFlagToSpec R n)

/-- The projection of `GLₙ ×_R (GLₙ ×_R Flₙ)` to the outer factor `Spec 𝒪(GLₙ)`. -/
def generalLinearFlagOuterCoordinate :
    generalLinearFlagDoubleProduct R n ⟶
      Spec (CommRingCat.of (GLCoord R n)) :=
  pullback.fst _ _

/-- The projection of `GLₙ ×_R (GLₙ ×_R Flₙ)` to the inner factor `GLₙ ×_R Flₙ`. -/
def generalLinearFlagInnerProduct :
    generalLinearFlagDoubleProduct R n ⟶
      generalLinearFlagProduct R n :=
  pullback.snd _ _

@[reassoc] theorem generalLinearFlagDouble_condition :
    generalLinearFlagOuterCoordinate R n ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (GLCoord R n))) =
    generalLinearFlagInnerProduct R n ≫
      generalLinearFlagToSpec R n :=
  pullback.condition

@[reassoc] theorem generalLinearFlagCoordinate_toSpec :
    generalLinearFlagCoordinateMap R n ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (GLCoord R n))) =
    generalLinearFlagToSpec R n := by
  unfold generalLinearFlagCoordinateMap
    generalLinearFlagToSpec
  rw [Category.assoc, ← TauCeti.GeneralLinear.groupScheme_X_hom]
  exact pullback.condition

/-- The two `GLₙ`-coordinates of `GLₙ ×_R (GLₙ ×_R Flₙ)`, as a point of
`Spec 𝒪(GLₙ) ×_R Spec 𝒪(GLₙ)`. -/
def generalLinearFlagCoordinatePair :
    generalLinearFlagDoubleProduct R n ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R (GLCoord R n))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (GLCoord R n)))) :=
  pullback.lift (generalLinearFlagOuterCoordinate R n)
    (generalLinearFlagInnerProduct R n ≫
      generalLinearFlagCoordinateMap R n) (by
        rw [Category.assoc, generalLinearFlagCoordinate_toSpec]
        exact generalLinearFlagDouble_condition R n)

@[reassoc] theorem generalLinearFlagCoordinatePair_outer :
    generalLinearFlagCoordinatePair R n ≫
      pullback.fst _ _ = generalLinearFlagOuterCoordinate R n :=
  pullback.lift_fst _ _ _

@[reassoc] theorem generalLinearFlagCoordinatePair_inner :
    generalLinearFlagCoordinatePair R n ≫
      pullback.snd _ _ = generalLinearFlagInnerProduct R n ≫
        generalLinearFlagCoordinateMap R n :=
  pullback.lift_snd _ _ _

/-- The two `GLₙ`-coordinates, as a point of `Spec (𝒪(GLₙ) ⊗_R 𝒪(GLₙ))`. -/
def generalLinearFlagTensorCoordinates :
    generalLinearFlagDoubleProduct R n ⟶
      Spec (CommRingCat.of ((GLCoord R n) ⊗[R] (GLCoord R n))) :=
  generalLinearFlagCoordinatePair R n ≫
    (pullbackSpecIso R (GLCoord R n) (GLCoord R n)).hom

/-- The product `g h` of the two `GLₙ`-coordinates, through the comultiplication of `𝒪(GLₙ)`. -/
def generalLinearFlagMultipliedCoordinate :
    generalLinearFlagDoubleProduct R n ⟶
      Spec (CommRingCat.of (GLCoord R n)) :=
  generalLinearFlagTensorCoordinates R n ≫
    Spec.map (CommRingCat.ofHom (TauCeti.GeneralLinear.comul R n).toRingHom)

@[reassoc] theorem generalLinearFlagMultipliedCoordinate_base :
    generalLinearFlagMultipliedCoordinate R n ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (GLCoord R n))) =
    generalLinearFlagOuterCoordinate R n ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (GLCoord R n))) := by
  have hc : Spec.map (CommRingCat.ofHom (TauCeti.GeneralLinear.comul R n).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (GLCoord R n))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap R ((GLCoord R n) ⊗[R] (GLCoord R n)))) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact (TauCeti.GeneralLinear.comul R n).commutes r
  unfold generalLinearFlagMultipliedCoordinate
    generalLinearFlagTensorCoordinates
  rw [Category.assoc, hc, Category.assoc,
    pullbackSpecIso_hom_base]
  unfold generalLinearFlagCoordinatePair
  rw [← Category.assoc, pullback.lift_fst]

/-- The point `(g h, V•)` of `GLₙ ×_R Flₙ` over `(g, h, V•)`. -/
def generalLinearFlagMultipliedPoint :
    generalLinearFlagDoubleProduct R n ⟶
      generalLinearFlagProduct R n :=
  pullback.lift
    (generalLinearFlagMultipliedCoordinate R n ≫
      (TauCeti.GeneralLinear.groupSchemeSpecIso R n).inv)
    (generalLinearFlagInnerProduct R n ≫
      generalLinearFlagPoint R n) (by
        rw [Category.assoc, TauCeti.GeneralLinear.groupScheme_X_hom,
          Iso.inv_hom_id_assoc,
          generalLinearFlagMultipliedCoordinate_base]
        rw [generalLinearFlagDouble_condition,
          Category.assoc]
        rfl)

/-- The point `(g, h · V•)` of `GLₙ ×_R Flₙ` over `(g, h, V•)`. -/
def generalLinearFlagSuccessivePoint :
    generalLinearFlagDoubleProduct R n ⟶
      generalLinearFlagProduct R n :=
  pullback.lift
    (generalLinearFlagOuterCoordinate R n ≫
      (TauCeti.GeneralLinear.groupSchemeSpecIso R n).inv)
    (generalLinearFlagInnerProduct R n ≫
      generalLinearFlagAction R n) (by
        rw [Category.assoc, TauCeti.GeneralLinear.groupScheme_X_hom,
          Iso.inv_hom_id_assoc]
        rw [generalLinearFlagDouble_condition,
          Category.assoc, generalLinearFlagAction_toSpec])

@[reassoc] theorem generalLinearFlagMultipliedPoint_group :
    generalLinearFlagMultipliedPoint R n ≫
      generalLinearFlagGroup R n =
    generalLinearFlagMultipliedCoordinate R n ≫
      (TauCeti.GeneralLinear.groupSchemeSpecIso R n).inv :=
  pullback.lift_fst _ _ _

@[reassoc] theorem generalLinearFlagMultipliedPoint_point :
    generalLinearFlagMultipliedPoint R n ≫
      generalLinearFlagPoint R n =
    generalLinearFlagInnerProduct R n ≫
      generalLinearFlagPoint R n :=
  pullback.lift_snd _ _ _

@[reassoc] theorem generalLinearFlagSuccessivePoint_group :
    generalLinearFlagSuccessivePoint R n ≫
      generalLinearFlagGroup R n =
    generalLinearFlagOuterCoordinate R n ≫
      (TauCeti.GeneralLinear.groupSchemeSpecIso R n).inv :=
  pullback.lift_fst _ _ _

@[reassoc] theorem generalLinearFlagSuccessivePoint_point :
    generalLinearFlagSuccessivePoint R n ≫
      generalLinearFlagPoint R n =
    generalLinearFlagInnerProduct R n ≫
      generalLinearFlagAction R n :=
  pullback.lift_snd _ _ _

/-- The morphism `(g, h, V•) ↦ (g h) · V•`. -/
def generalLinearFlagMultipliedAction :
    generalLinearFlagDoubleProduct R n ⟶
      selectedFlagChartScheme R n :=
  generalLinearFlagMultipliedPoint R n ≫
    generalLinearFlagAction R n

/-- The morphism `(g, h, V•) ↦ g · (h · V•)`. -/
def generalLinearFlagSuccessiveAction :
    generalLinearFlagDoubleProduct R n ⟶
      selectedFlagChartScheme R n :=
  generalLinearFlagSuccessivePoint R n ≫
    generalLinearFlagAction R n

variable (B : Type u) [CommRing B] [Algebra R B]

/-- The `B`-point `(g, h, P)` of `GLₙ ×_R (GLₙ ×_R Flₙ)` given by two `R`-algebra maps
`k, l : 𝒪(GLₙ) → B` and a flag `P` of `Bⁿ`. -/
def generalLinearFlagDoubleOfAffine
    (k l : GLCoord R n →ₐ[R] B)
    (P : RingFlag B (Fin n → B) n) :
    Spec (CommRingCat.of B) ⟶ generalLinearFlagDoubleProduct R n :=
  pullback.lift (Spec.map (CommRingCat.ofHom k.toRingHom))
    (generalLinearFlagOfAffine R B n l P) (by
      rw [generalLinearFlagToSpec, ← Category.assoc,
        generalLinearFlagOfAffine_point,
        simultaneousFlagRelativeMorphism_toSpec]
      rw [← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro r
      exact k.commutes r)

@[reassoc] theorem generalLinearFlagDoubleOfAffine_outer
    (k l : GLCoord R n →ₐ[R] B)
    (P : RingFlag B (Fin n → B) n) :
    generalLinearFlagDoubleOfAffine R n B k l P ≫
      generalLinearFlagOuterCoordinate R n =
      Spec.map (CommRingCat.ofHom k.toRingHom) :=
  pullback.lift_fst _ _ _

@[reassoc] theorem generalLinearFlagDoubleOfAffine_inner
    (k l : GLCoord R n →ₐ[R] B)
    (P : RingFlag B (Fin n → B) n) :
    generalLinearFlagDoubleOfAffine R n B k l P ≫
      generalLinearFlagInnerProduct R n =
      generalLinearFlagOfAffine R B n l P :=
  pullback.lift_snd _ _ _

private theorem generalLinearFlagCoordinatePair_affine
    (k l : GLCoord R n →ₐ[R] B)
    (P : RingFlag B (Fin n → B) n) :
    generalLinearFlagDoubleOfAffine R n B k l P ≫
        generalLinearFlagCoordinatePair R n =
      Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.lift k l (fun _ _ => Commute.all _ _)).toRingHom) ≫
        (pullbackSpecIso R (GLCoord R n) (GLCoord R n)).inv := by
  apply pullback.hom_ext
  · rw [Category.assoc, generalLinearFlagCoordinatePair_outer,
      generalLinearFlagDoubleOfAffine_outer,
      Category.assoc, pullbackSpecIso_inv_fst,
      ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact (congrArg AlgHom.toRingHom
      (Algebra.TensorProduct.lift_comp_includeLeft k l (fun _ _ => Commute.all _ _))).symm
  · rw [Category.assoc, generalLinearFlagCoordinatePair_inner,
      ← Category.assoc, generalLinearFlagDoubleOfAffine_inner,
      generalLinearFlagOfAffine_coordinate,
      Category.assoc, pullbackSpecIso_inv_snd,
      ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact (congrArg AlgHom.toRingHom
      (Algebra.TensorProduct.lift_comp_includeRight k l (fun _ _ => Commute.all _ _))).symm

@[reassoc] theorem generalLinearFlagTensorCoordinates_affine
    (k l : GLCoord R n →ₐ[R] B)
    (P : RingFlag B (Fin n → B) n) :
    generalLinearFlagDoubleOfAffine R n B k l P ≫
      generalLinearFlagTensorCoordinates R n =
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.lift k l (fun _ _ => Commute.all _ _)).toRingHom) := by
  unfold generalLinearFlagTensorCoordinates
  rw [← Category.assoc, generalLinearFlagCoordinatePair_affine,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

@[reassoc] theorem generalLinearFlagMultipliedCoordinate_affine
    (k l : GLCoord R n →ₐ[R] B)
    (P : RingFlag B (Fin n → B) n) :
    generalLinearFlagDoubleOfAffine R n B k l P ≫
      generalLinearFlagMultipliedCoordinate R n =
    Spec.map (CommRingCat.ofHom
      (generalLinearAlgebraPointMul R B n k l).toRingHom) := by
  unfold generalLinearFlagMultipliedCoordinate
  rw [← Category.assoc, generalLinearFlagTensorCoordinates_affine,
    ← Spec.map_comp]
  rfl

private theorem generalLinearFlagMultipliedPoint_affine
    (k l : GLCoord R n →ₐ[R] B)
    (P : RingFlag B (Fin n → B) n) :
    generalLinearFlagDoubleOfAffine R n B k l P ≫
      generalLinearFlagMultipliedPoint R n =
    generalLinearFlagOfAffine R B n
      (generalLinearAlgebraPointMul R B n k l) P := by
  apply pullback.hom_ext
  · change (generalLinearFlagDoubleOfAffine R n B k l P ≫
        generalLinearFlagMultipliedPoint R n) ≫
        generalLinearFlagGroup R n = _
    rw [Category.assoc]
    rw [generalLinearFlagMultipliedPoint_group, ← Category.assoc,
      generalLinearFlagMultipliedCoordinate_affine]
    exact (generalLinearFlagOfAffine_group R B n
      (generalLinearAlgebraPointMul R B n k l) P).symm
  · change (generalLinearFlagDoubleOfAffine R n B k l P ≫
        generalLinearFlagMultipliedPoint R n) ≫
        generalLinearFlagPoint R n = _
    rw [Category.assoc]
    rw [generalLinearFlagMultipliedPoint_point, ← Category.assoc,
      generalLinearFlagDoubleOfAffine_inner,
      generalLinearFlagOfAffine_point]
    exact (generalLinearFlagOfAffine_point R B n
      (generalLinearAlgebraPointMul R B n k l) P).symm

private theorem generalLinearFlagSuccessivePoint_affine
    (k l : GLCoord R n →ₐ[R] B)
    (P : RingFlag B (Fin n → B) n) :
    generalLinearFlagDoubleOfAffine R n B k l P ≫
      generalLinearFlagSuccessivePoint R n =
    generalLinearFlagOfAffine R B n k
      (RingFlag.transport P
        ((generalLinearMatrixAt R B n l).toLinearEquiv'
          (generalLinearMatrixAt_isUnit R B n l).invertible)) := by
  apply pullback.hom_ext
  · change (generalLinearFlagDoubleOfAffine R n B k l P ≫
        generalLinearFlagSuccessivePoint R n) ≫
        generalLinearFlagGroup R n = _
    rw [Category.assoc]
    rw [generalLinearFlagSuccessivePoint_group, ← Category.assoc,
      generalLinearFlagDoubleOfAffine_outer]
    exact (generalLinearFlagOfAffine_group R B n k _).symm
  · change (generalLinearFlagDoubleOfAffine R n B k l P ≫
        generalLinearFlagSuccessivePoint R n) ≫
        generalLinearFlagPoint R n = _
    rw [Category.assoc]
    rw [generalLinearFlagSuccessivePoint_point, ← Category.assoc,
      generalLinearFlagDoubleOfAffine_inner,
      generalLinearFlagAction_evaluate]
    exact (generalLinearFlagOfAffine_point R B n k _).symm

/-- The two composite scheme morphisms agree after every affine
algebra evaluation, with matrix order fixed by the Hopf comultiplication. -/
theorem generalLinearFlagAction_mul_affine_test
    (k l : GLCoord R n →ₐ[R] B)
    (P : RingFlag B (Fin n → B) n) :
    generalLinearFlagDoubleOfAffine R n B k l P ≫
      generalLinearFlagMultipliedAction R n =
    generalLinearFlagDoubleOfAffine R n B k l P ≫
      generalLinearFlagSuccessiveAction R n := by
  unfold generalLinearFlagMultipliedAction
    generalLinearFlagSuccessiveAction
  rw [← Category.assoc, generalLinearFlagMultipliedPoint_affine,
    ← Category.assoc, generalLinearFlagSuccessivePoint_affine]
  exact (generalLinearFlagAction_mul_affine R B n k l P).symm

end FlagVarieties.Foundations.QuotientCharts

