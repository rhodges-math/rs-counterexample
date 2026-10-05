import Schubert.FlagVarieties.Foundations.Schemes.GeneralLinearFlagLawsMulExt

/-! The raw determinant-localization product used in the Flag law
is exactly multiplication in the original Tau Ceti GL group scheme. -/

noncomputable section
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonObj MonoidalCategory WithConv
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ)

/-- The two `GLₙ`-coordinates of `GLₙ ×_R (GLₙ ×_R Flₙ)`, as a point of `GLₙ ×_R GLₙ`. -/
def generalLinearFlagGroupPair :
    generalLinearFlagDoubleProduct R n ⟶
      (((TauCeti.GeneralLinear.groupScheme R n).X ⊗
        (TauCeti.GeneralLinear.groupScheme R n).X).left) :=
  generalLinearFlagTensorCoordinates R n ≫
    (TauCeti.GeneralLinear.groupSchemeMulSourceIso R n).inv

@[reassoc] theorem generalLinearFlagGroupPair_mul :
    generalLinearFlagGroupPair R n ≫
      μ[(TauCeti.GeneralLinear.groupScheme R n).X].left =
    generalLinearFlagMultipliedCoordinate R n ≫
      (TauCeti.GeneralLinear.groupSchemeSpecIso R n).inv := by
  rw [TauCeti.GeneralLinear.groupScheme_mul_left]
  unfold generalLinearFlagGroupPair
    generalLinearFlagMultipliedCoordinate
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

variable (B : Type u) [CommRing B] [Algebra R B]

@[reassoc] theorem generalLinearFlagGroupPair_affine
    (k l : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] B)
    (P : RingFlag B (Fin n → B) n) :
    generalLinearFlagDoubleOfAffine R n B k l P ≫
      generalLinearFlagGroupPair R n =
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.lift k l (fun _ _ => Commute.all _ _)).toRingHom) ≫
      (TauCeti.GeneralLinear.groupSchemeMulSourceIso R n).inv := by
  unfold generalLinearFlagGroupPair
  rw [← Category.assoc, generalLinearFlagTensorCoordinates_affine]

@[reassoc] theorem generalLinearFlagGroupPair_mul_affine
    (k l : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] B)
    (P : RingFlag B (Fin n → B) n) :
    (generalLinearFlagDoubleOfAffine R n B k l P ≫
      generalLinearFlagGroupPair R n) ≫
      μ[(TauCeti.GeneralLinear.groupScheme R n).X].left =
    generalLinearGroupPoint R B n (generalLinearAlgebraPointMul R B n k l) := by
  rw [Category.assoc, generalLinearFlagGroupPair_mul,
    ← Category.assoc, generalLinearFlagMultipliedCoordinate_affine]
  rfl

end FlagVarieties.Foundations.QuotientCharts

