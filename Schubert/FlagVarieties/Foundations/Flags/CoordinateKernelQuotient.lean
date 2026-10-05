import Schubert.FlagVarieties.Foundations.Flags.CoordinateLocalizationKernels

/-!
# Tensor quotients of arbitrary coordinate kernels

Right exactness identifies the tensor of the quotient by any submodule
with the quotient by the scalar-extended kernel in the original coordinates.
No finite projectivity of the quotient is required for this comparison.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

open TensorProduct

variable {A : Type*} [CommRing A] (B : Type*) [CommRing B] [Algebra A B]
  {n : ℕ} (K : Submodule A (Fin n → A))

/-- Tensor the quotient map and retain the original coordinate ordering. -/
def coordinateKernelTensorQuotientMap :
    (Fin n → B) →ₗ[B] (B ⊗[A] ((Fin n → A) ⧸ K)) :=
  (K.mkQ.baseChange B).comp (TensorProduct.piScalarRight A B B (Fin n)).symm.toLinearMap

theorem coordinateKernelTensorQuotientMap_surjective :
    Function.Surjective (coordinateKernelTensorQuotientMap B K) :=
  (LinearMap.baseChange_surjective B K.mkQ_surjective).comp
    (TensorProduct.piScalarRight A B B (Fin n)).symm.surjective

/-- The tensor quotient has the expected kernel by right exactness. -/
theorem coordinateKernelTensorQuotientMap_ker :
    LinearMap.ker (coordinateKernelTensorQuotientMap B K) =
      (K.baseChange B).map (TensorProduct.piScalarRight A B B (Fin n)).toLinearMap := by
  rw [coordinateKernelTensorQuotientMap, LinearMap.ker_comp, baseChange_mkQ_ker]
  exact ((K.baseChange B).map_equiv_eq_comap_symm
    (TensorProduct.piScalarRight A B B (Fin n))).symm

/-- Canonical comparison used before finite projectivity of the global quotient is known. -/
def coordinateKernelTensorQuotientEquiv :
    (B ⊗[A] ((Fin n → A) ⧸ K)) ≃ₗ[B]
      ((Fin n → B) ⧸ (K.baseChange B).map
        (TensorProduct.piScalarRight A B B (Fin n)).toLinearMap) :=
  ((coordinateKernelTensorQuotientMap B K).quotKerEquivOfSurjective
    (coordinateKernelTensorQuotientMap_surjective B K)).symm.trans
      (Submodule.quotEquivOfEq _ _ (coordinateKernelTensorQuotientMap_ker B K))

end FlagVarieties.Foundations.QuotientCharts
