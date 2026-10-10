import RSCounterexample.FlagVarieties.Foundations.Schemes.GeneralLinearFlagLawsUnit
import RSCounterexample.FlagVarieties.Foundations.Schemes.GeneralLinearGrassmannianLawsMatrix

/-! Composition of the varying flag action on every affine algebra point. -/

noncomputable section
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory Matrix
universe u
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] (n : ℕ)

private theorem generalLinearMatrixAt_mul_equiv_flag
    (k l : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] B) :
    ((generalLinearMatrixAt R B n l).toLinearEquiv'
      (generalLinearMatrixAt_isUnit R B n l).invertible).trans
      ((generalLinearMatrixAt R B n k).toLinearEquiv'
        (generalLinearMatrixAt_isUnit R B n k).invertible) =
    (generalLinearMatrixAt R B n (generalLinearAlgebraPointMul R B n k l)).toLinearEquiv'
      (generalLinearMatrixAt_isUnit R B n
        (generalLinearAlgebraPointMul R B n k l)).invertible := by
  apply LinearEquiv.ext
  intro x
  change generalLinearMatrixAt R B n k *ᵥ (generalLinearMatrixAt R B n l *ᵥ x) =
    generalLinearMatrixAt R B n (generalLinearAlgebraPointMul R B n k l) *ᵥ x
  rw [generalLinearMatrixAt_mul, Matrix.mulVec_mulVec]

theorem generalLinearFlagAction_mul_affine
    (k l : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] B)
    (P : RingFlag B (Fin n → B) n) :
    generalLinearFlagOfAffine R B n k
        (RingFlag.transport P
          ((generalLinearMatrixAt R B n l).toLinearEquiv'
            (generalLinearMatrixAt_isUnit R B n l).invertible)) ≫
      generalLinearFlagAction R n =
    generalLinearFlagOfAffine R B n
        (generalLinearAlgebraPointMul R B n k l) P ≫
      generalLinearFlagAction R n := by
  rw [generalLinearFlagAction_evaluate,
    generalLinearFlagAction_evaluate,
    RingFlag.transport_trans,
    generalLinearMatrixAt_mul_equiv_flag]

end FlagVarieties.Foundations.QuotientCharts
