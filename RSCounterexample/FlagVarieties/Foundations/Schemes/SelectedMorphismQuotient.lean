import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedMorphismQuotientFrames
import RSCounterexample.FlagVarieties.Foundations.Flags.LocalQuotientProjectivity
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedQuotientMorphismInjective

/-!
# The quotient recovered from an affine scheme morphism

The finite presentation cover determines a global kernel. Its local
quotient frames prove finite projectivity and the required stalk rank.
The induced scheme map is the original incoming map, so injectivity also
proves independence of every choice in the reconstruction.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts.SelectedMorphismCover

open AlgebraicGeometry CategoryTheory

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {n d : ℕ}
  {F : Spec (CommRingCat.of A) ⟶ selectedChartScheme R n d}
  (D : SelectedMorphismCover F) [Finite D.index]

/-- The descended finite-projective quotient with the original global kernel. -/
def quotient : Module.Grassmannian A (Fin n → A) d :=
  grassmannianOfPrincipalQuotientFrames D.kernel D.element D.span_top D.kernelLocalFrame

@[simp] theorem quotient_submodule : D.quotient.toSubmodule = D.kernel := rfl

/-- Scalar extension recovers each of the local quotients originally extracted from the map. -/
theorem quotient_baseChange (i : D.index) :
    coordinateGrassmannianBaseChange (Localization.Away (D.element i)) D.quotient =
      selectedChartPoint R (D.selection i) (D.evaluation i) := by
  apply Module.Grassmannian.ext
  rw [coordinateGrassmannianBaseChange_submodule, quotient_submodule,
    ← coordinate_localized_submodule (.powers (D.element i)), D.kernel_localized_eq]

/-- The original presentation cover presents the constructed global quotient. -/
def quotientCover : SelectedQuotientCover R A D.quotient where
  index := D.index
  element := D.element
  selection := D.selection
  span_top := D.span_top
  evaluation := D.evaluation
  represents i := (D.quotient_baseChange i).symm

/-- Gluing the recovered quotient returns the full original scheme morphism. -/
theorem quotient_morphism : selectedQuotientMorphism R D.quotient = F := by
  apply D.quotientCover.schemeCover.hom_ext
  intro i
  exact (D.quotientCover.ι_selectedQuotientMorphism i).trans (D.factors i)

/-- Different finite presentation covers recover the same quotient kernel. -/
theorem quotient_independent (E : SelectedMorphismCover F) [Finite E.index] :
    D.quotient = E.quotient := by
  apply selectedQuotientMorphism_injective (R := R)
  rw [D.quotient_morphism, E.quotient_morphism]

end FlagVarieties.Foundations.QuotientCharts.SelectedMorphismCover
