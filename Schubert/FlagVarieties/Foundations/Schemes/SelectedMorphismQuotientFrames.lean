import Schubert.FlagVarieties.Foundations.Schemes.SelectedMorphismKernelDescent
import Schubert.FlagVarieties.Foundations.Flags.CoordinateKernelQuotient

/-!
# Local frames of the quotient recovered from an incoming morphism

Kernel descent and right exactness give local frames of the
global quotient. Finite projectivity is not assumed in making these frames.
Their basis vectors are the original selected coordinate images.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts.SelectedMorphismCover

open AlgebraicGeometry CategoryTheory TensorProduct

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {n d : ℕ}
  {F : Spec (CommRingCat.of A) ⟶ selectedChartScheme R n d}
  (D : SelectedMorphismCover F) [Finite D.index]

/-- The tensor of the recovered quotient is the selected local quotient. -/
def kernelLocalQuotientEquiv (i : D.index) :
    (Localization.Away (D.element i) ⊗[A] ((Fin n → A) ⧸ D.kernel))
      ≃ₗ[Localization.Away (D.element i)]
      ((Fin n → Localization.Away (D.element i)) ⧸
        (selectedChartPoint R (D.selection i) (D.evaluation i)).toSubmodule) :=
  (coordinateKernelTensorQuotientEquiv (Localization.Away (D.element i)) D.kernel).trans
    (Submodule.quotEquivOfEq _ _ (by
      rw [← coordinate_localized_submodule (.powers (D.element i)), D.kernel_localized_eq]))

/-- The original selected coordinate map supplies a free frame of the local tensor quotient. -/
def kernelLocalFrame (i : D.index) :
    (Localization.Away (D.element i) ⊗[A] ((Fin n → A) ⧸ D.kernel))
      ≃ₗ[Localization.Away (D.element i)]
      (Fin d → Localization.Away (D.element i)) :=
  (D.kernelLocalQuotientEquiv i).trans
    (LinearEquiv.ofBijective
      ((selectedChartPoint R (D.selection i) (D.evaluation i)).toSubmodule.mkQ.comp
        (coordinateInclusion (D.selection i)))
      (selectedChartPoint_selected_bijective R (D.selection i) (D.evaluation i))).symm

end FlagVarieties.Foundations.QuotientCharts.SelectedMorphismCover
