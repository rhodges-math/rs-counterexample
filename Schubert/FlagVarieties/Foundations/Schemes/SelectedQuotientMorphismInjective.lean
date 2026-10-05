import Schubert.FlagVarieties.Foundations.Schemes.SelectedQuotientMorphismPresentation
import Schubert.FlagVarieties.Foundations.Schemes.SelectedQuotientMorphismNaturality
import Schubert.FlagVarieties.Foundations.Flags.CoordinateQuotientLocalEquality

/-!
# The intrinsic quotient-to-scheme map is injective

Equality of full scheme morphisms detects the quotient kernel.
First compare an arbitrary quotient with a globally presented chart point;
then apply that comparison on a principal presentation cover of either
quotient. Local detection of submodule equality supplies the global result.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {n d : ℕ}

/-- Equality with a globally selected chart map determines the quotient. -/
theorem selectedQuotient_eq_point_of_map_eq
    (P : Module.Grassmannian A (Fin n → A) d) (a : Fin d ↪ Fin n)
    (f : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A)
    (h : selectedQuotientMorphism R P = selectedChartPointMap R a f) :
    P = selectedChartPoint R a f := by
  let D := selectedQuotientCover R A P
  apply coordinateGrassmannian_eq_of_baseChange_away_eq D.element D.span_top
  intro i
  have hi := congrArg (fun q : Spec (CommRingCat.of A) ⟶ selectedChartScheme R n d =>
    D.schemeCover.f i ≫ q) h
  rw [D.ι_selectedQuotientMorphism] at hi
  change selectedChartPointMap R (D.selection i) (D.evaluation i) =
    Spec.map (CommRingCat.ofHom
      (IsScalarTower.toAlgHom R A (Localization.Away (D.element i))).toRingHom) ≫
      selectedChartPointMap R a f at hi
  rw [selectedChartPointMap_comp] at hi
  rw [← D.represents, selectedChartPoint_baseChange_tower]
  exact selectedChartPoint_quotient_eq_of_map_eq R (D.selection i) a _ _ hi

/-- Different finite-projective quotient kernels cannot give the same scheme morphism. -/
theorem selectedQuotientMorphism_injective :
    Function.Injective (selectedQuotientMorphism R (A := A) (n := n) (d := d)) := by
  intro P Q h
  let D := selectedQuotientCover R A P
  apply coordinateGrassmannian_eq_of_baseChange_away_eq D.element D.span_top
  intro i
  have hlocal : selectedQuotientMorphism R
      (coordinateGrassmannianBaseChange (Localization.Away (D.element i)) Q) =
      selectedChartPointMap R (D.selection i) (D.evaluation i) := by
    rw [← selectedQuotientMorphism_baseChange Q, ← h]
    exact D.ι_selectedQuotientMorphism i
  exact (D.represents i).symm.trans
    (selectedQuotient_eq_point_of_map_eq _ (D.selection i) (D.evaluation i) hlocal).symm

/-- The intrinsic map retains exactly equality of the original quotients. -/
theorem selectedQuotientMorphism_eq_iff
    (P Q : Module.Grassmannian A (Fin n → A) d) :
    selectedQuotientMorphism R P = selectedQuotientMorphism R Q ↔ P = Q :=
  ⟨fun h => selectedQuotientMorphism_injective h,
    fun h => congrArg (selectedQuotientMorphism R) h⟩

end FlagVarieties.Foundations.QuotientCharts
