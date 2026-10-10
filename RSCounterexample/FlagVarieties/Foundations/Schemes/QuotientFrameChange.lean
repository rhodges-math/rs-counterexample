import RSCounterexample.FlagVarieties.Foundations.Flags.SplitModules
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Change of frame for a free module of rank one

For two linear isomorphisms `frame, frame' : Q ≃ₗ[R] R`, the coordinates `frame x` and
`frame' x` differ by the common unit `frame' (frame.symm 1)`.
-/

namespace FlagVarieties.Foundations

section RingCoordinates

variable {K Q : Type*} [CommRing K] [AddCommGroup Q] [Module K Q]

/-- Coordinates in two frames differ by a common scalar. -/
theorem quotient_frame_change (frame frame' : Q ≃ₗ[K] K) (x : Q) :
    frame' x = frame' (frame.symm 1) * frame x := by
  have hx : x = frame x • frame.symm 1 := by
    apply frame.injective
    simp
  calc
    frame' x = frame' (frame x • frame.symm 1) := congrArg frame' hx
    _ = frame x * frame' (frame.symm 1) := by rw [map_smul]; rfl
    _ = frame' (frame.symm 1) * frame x := mul_comm _ _

end RingCoordinates

variable {R Q : Type*} [CommRing R] [AddCommGroup Q] [Module R Q]

/-- The inverse frame change supplies an explicit multiplicative inverse. -/
theorem quotient_frame_change_factor_isUnit (frame frame' : Q ≃ₗ[R] R) :
    IsUnit (frame' (frame.symm 1)) := by
  apply IsUnit.of_mul_eq_one (frame (frame'.symm 1))
  simpa only [LinearEquiv.apply_symm_apply] using
    (quotient_frame_change frame frame' (frame'.symm 1)).symm

/-- Two coordinates transform by the same unit. -/
theorem quotient_frame_change_pair (frame frame' : Q ≃ₗ[R] R) (x y : Q) :
    ∃ u : Rˣ, frame' x = (u : R) * frame x ∧ frame' y = (u : R) * frame y := by
  obtain ⟨u, hu⟩ := quotient_frame_change_factor_isUnit frame frame'
  refine ⟨u, ?_, ?_⟩
  · rw [hu]
    exact quotient_frame_change frame frame' x
  · rw [hu]
    exact quotient_frame_change frame frame' y

end FlagVarieties.Foundations
