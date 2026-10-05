import Schubert.FlagVarieties.Foundations.Flags.QuotientChartTransition

/-!
# Determinant formulas for the chart transitions

The inverse selected block in a normalized quotient transition is its
ordinary nonsingular matrix inverse. Thus every new coordinate is an
adjugate expression divided by the selected determinant. Scalar extension
preserves this expression whenever the determinant is a unit. These are
ring-level formulas; no scheme coverage or representability is assumed.
-/

namespace FlagVarieties.Foundations.QuotientCharts

variable {R : Type*} [CommRing R] {d c : ℕ}

/-- The matrix of the inverse equivalence is the nonsingular inverse. -/
theorem toMatrix_symm (e : (Fin d → R) ≃ₗ[R] (Fin d → R)) :
    LinearMap.toMatrix' e.symm.toLinearMap = (LinearMap.toMatrix' e.toLinearMap)⁻¹ := by
  apply Eq.symm
  apply Matrix.inv_eq_left_inv
  rw [← LinearMap.toMatrix'_comp]
  have he : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by ext x; simp
  rw [he, LinearMap.toMatrix'_id]

/-- Matrix form of the previously constructed, quotient transition. -/
theorem toMatrix_transition (C : Matrix (Fin d) (Fin c) R)
    (e : ((Fin d → R) × (Fin c → R)) ≃ₗ[R] ((Fin d → R) × (Fin c → R)))
    (h : Function.Bijective (selectedBlock (Matrix.toLin' C) e)) :
    LinearMap.toMatrix' (transition (Matrix.toLin' C) e h) =
      (LinearMap.toMatrix' (selectedBlock (Matrix.toLin' C) e))⁻¹ *
        LinearMap.toMatrix' (remainingBlock (Matrix.toLin' C) e) := by
  rw [transition, LinearMap.toMatrix'_comp, toMatrix_symm]
  rfl

/-- The denominator is precisely the selected-block determinant. -/
theorem toMatrix_transition_adjugate (C : Matrix (Fin d) (Fin c) R)
    (e : ((Fin d → R) × (Fin c → R)) ≃ₗ[R] ((Fin d → R) × (Fin c → R)))
    (h : Function.Bijective (selectedBlock (Matrix.toLin' C) e)) :
    LinearMap.toMatrix' (transition (Matrix.toLin' C) e h) =
      Ring.inverse (LinearMap.toMatrix' (selectedBlock (Matrix.toLin' C) e)).det •
        ((LinearMap.toMatrix' (selectedBlock (Matrix.toLin' C) e)).adjugate *
          LinearMap.toMatrix' (remainingBlock (Matrix.toLin' C) e)) := by
  rw [toMatrix_transition, Matrix.inv_def, Matrix.smul_mul]

/-- Nonsingular inversion commutes with every ring map on the unit-determinant locus. -/
theorem map_matrix_inverse_of_isUnit_det {S : Type*} [CommRing S]
    (f : R →+* S) (L : Matrix (Fin d) (Fin d) R) (h : IsUnit L.det) :
    (L⁻¹).map f = (L.map f)⁻¹ := by
  apply Eq.symm
  apply Matrix.inv_eq_left_inv
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul,
    Matrix.nonsing_inv_mul _ h, map_one]

/-- The inverse-block formula itself is natural under arbitrary scalar extension. -/
theorem map_matrix_transition_of_isUnit_det {S : Type*} [CommRing S]
    (f : R →+* S) (L : Matrix (Fin d) (Fin d) R)
    (N : Matrix (Fin d) (Fin c) R) (h : IsUnit L.det) :
    (L⁻¹ * N).map f = (L.map f)⁻¹ * N.map f := by
  rw [Matrix.map_mul, map_matrix_inverse_of_isUnit_det f L h]

end FlagVarieties.Foundations.QuotientCharts
