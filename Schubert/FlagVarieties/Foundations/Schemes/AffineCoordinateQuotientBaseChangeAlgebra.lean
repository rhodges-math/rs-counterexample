import Schubert.FlagVarieties.Foundations.Schemes.AffineTildePullbackNaturality
import Schubert.FlagVarieties.Foundations.Flags.CoordinateBaseChange

/-!
# Scalar extension of the original finite-coordinate quotient

The existing `coordinateQuotientEquiv` identifies the quotient by the
base-changed kernel with the tensor extension of the original quotient.
Here it is oriented toward the new quotient and its defining equation is
proved with the original ambient quotient maps.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

open TensorProduct CategoryTheory

universe u

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
  {n d : ℕ} (P : Module.Grassmannian R (Fin n → R) d)

/-- The canonical tensor model of the original labelled ambient coordinates. -/
abbrev coordinateTensorFreeEquiv :
    B ⊗[R] (Fin n → R) ≃ₗ[B] (Fin n → B) :=
  TensorProduct.piScalarRight R B B (Fin n)

/-- The scalar-extended quotient, viewed as the new coordinate quotient. -/
def coordinateTensorQuotientEquiv :
    B ⊗[R] ((Fin n → R) ⧸ P.toSubmodule) ≃ₗ[B]
      ((Fin n → B) ⧸ (coordinateGrassmannianBaseChange B P).toSubmodule) :=
  (coordinateQuotientEquiv B P).symm

/-- The quotient comparison preserves the original ambient quotient map on
every tensor-extended coordinate vector. No flatness is used. -/
theorem coordinateTensorQuotientEquiv_source :
    (coordinateTensorQuotientEquiv R B P).toLinearMap.comp
        (P.toSubmodule.mkQ.baseChange B) =
      (coordinateGrassmannianBaseChange B P).toSubmodule.mkQ.comp
        (coordinateTensorFreeEquiv R B (n := n)).toLinearMap := by
  apply LinearMap.ext
  intro z
  apply (coordinateQuotientEquiv B P).injective
  change (coordinateQuotientEquiv B P)
      ((coordinateQuotientEquiv B P).symm (P.toSubmodule.mkQ.baseChange B z)) =
    (coordinateQuotientMap B P).quotKerEquivOfSurjective
      (coordinateQuotientMap_surjective B P)
        (Submodule.Quotient.mk ((coordinateTensorFreeEquiv R B (n := n)) z))
  rw [LinearEquiv.apply_symm_apply]
  rw [LinearMap.quotKerEquivOfSurjective_apply_mk]
  change P.toSubmodule.mkQ.baseChange B z =
    P.toSubmodule.mkQ.baseChange B
      ((TensorProduct.piScalarRight R B B (Fin n)).symm
        ((TensorProduct.piScalarRight R B B (Fin n)) z))
  rw [LinearEquiv.symm_apply_apply]

end FlagVarieties.Foundations.QuotientCharts
