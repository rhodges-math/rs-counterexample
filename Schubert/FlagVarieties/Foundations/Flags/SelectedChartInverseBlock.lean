import Schubert.FlagVarieties.Foundations.Flags.SelectedChartNaturality

/-! # The reverse selected block is the inverse forward block

This identity controls the determinant on a chart intersection. It will
supply the inverse denominator from the coordinates of the second chart.
-/

namespace FlagVarieties.Foundations.QuotientCharts

variable {R U V : Type*} [CommRing R]
  [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]

theorem selectedBlock_transition_symm (C : V →ₗ[R] U)
    (e : (U × V) ≃ₗ[R] (U × V))
    (h : Function.Bijective (selectedBlock C e)) :
    selectedBlock (transition C e h) e.symm =
      (LinearEquiv.ofBijective (selectedBlock C e) h).symm.toLinearMap := by
  ext u
  change normalizedMap (transition C e h) (e (u, 0)) = _
  rw [normalizedMap_transition]
  simp

theorem selectedCoordinateChange_symm {n d : ℕ} (a b : Fin d ↪ Fin n) :
    (selectedCoordinateChange (R := R) a b).symm = selectedCoordinateChange b a := rfl

/-- Matrix identity over every commutative ring, including rank zero. -/
theorem selectedBlock_transition_matrix {n d : ℕ}
    (C : Matrix (Fin d) (Fin (n-d)) R) (a b : Fin d ↪ Fin n)
    (h : Function.Bijective (selectedBlock (Matrix.toLin' C) (selectedCoordinateChange a b))) :
    LinearMap.toMatrix' (selectedBlock
      (transition (Matrix.toLin' C) (selectedCoordinateChange a b) h)
      (selectedCoordinateChange b a)) =
        (LinearMap.toMatrix' (selectedBlock (Matrix.toLin' C)
          (selectedCoordinateChange a b)))⁻¹ := by
  rw [← selectedCoordinateChange_symm a b, selectedBlock_transition_symm, toMatrix_symm]
  rfl

end FlagVarieties.Foundations.QuotientCharts
