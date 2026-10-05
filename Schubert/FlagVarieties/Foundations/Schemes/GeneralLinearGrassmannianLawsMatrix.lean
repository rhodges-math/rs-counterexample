import Schubert.FlagVarieties.Foundations.Schemes.GeneralLinearGrassmannianLawsUnitScheme

/-! Raw-coordinate multiplication of the generic general-linear matrix
after evaluation in any coefficient algebra. -/

noncomputable section
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory Matrix
open scoped TensorProduct
universe u
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] (n : ℕ)

/-- The product of two `B`-points `k`, `l` of `GLₙ`, through the comultiplication of `𝒪(GLₙ)`. -/
def generalLinearAlgebraPointMul
    (k l : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] B) :
    TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] B :=
  (Algebra.TensorProduct.lift k l (fun _ _ => Commute.all _ _)).comp
    (TauCeti.GeneralLinear.comul R n)

theorem generalLinearMatrixAt_mul
    (k l : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] B) :
    generalLinearMatrixAt R B n (generalLinearAlgebraPointMul R B n k l) =
      generalLinearMatrixAt R B n k * generalLinearMatrixAt R B n l := by
  let t := Algebra.TensorProduct.lift k l (fun _ _ => Commute.all _ _)
  calc
    generalLinearMatrixAt R B n (generalLinearAlgebraPointMul R B n k l) =
        ((TauCeti.GeneralLinear.localizedGenericMatrix R n).map
          (TauCeti.GeneralLinear.comul R n)).map t := by
      ext i j
      rfl
    _ = (((TauCeti.GeneralLinear.localizedGenericMatrix R n).map
          (Algebra.TensorProduct.includeLeft :
            TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] _)) *
        ((TauCeti.GeneralLinear.localizedGenericMatrix R n).map
          (Algebra.TensorProduct.includeRight :
            TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] _))).map t := by
      rw [TauCeti.GeneralLinear.map_comul_localizedGenericMatrix]
    _ = generalLinearMatrixAt R B n k * generalLinearMatrixAt R B n l := by
      rw [Matrix.map_mul]
      congr 1 <;> ext i j <;> simp [t, generalLinearMatrixAt]

end FlagVarieties.Foundations.QuotientCharts
