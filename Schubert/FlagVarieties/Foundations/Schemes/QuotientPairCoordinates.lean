import Schubert.FlagVarieties.Foundations.Schemes.QuotientFrameChange
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Coordinates derived from two-generator quotient modules

A surjection from the ordered free pair supplies the two quotient elements.
After any scalar extension, a frame of that extended module gives a
coprime coordinate pair. Frame extension is constructed by the tensor tower
equivalence; no local coordinates or transition units are assumed.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientPair

open TensorProduct

variable {R S T Q : Type*} [CommRing R] [CommRing S] [CommRing T]
  [AddCommGroup Q] [Module R Q] [Algebra R S]

theorem pair_decomposition (q : R × R →ₗ[R] Q) (a b : R) :
    q (a, b) = a • q (1, 0) + b • q (0, 1) := by
  have h : (a, b) = a • ((1, 0) : R × R) + b • ((0, 1) : R × R) := by ext <;> simp
  rw [h, map_add, map_smul, map_smul]

/-- The two quotient elements still generate after arbitrary scalar extension. -/
theorem extended_pair_generates (q : R × R →ₗ[R] Q) (hq : Function.Surjective q)
    (z : S ⊗[R] Q) :
    ∃ a b : S, z = a • (1 ⊗ₜ[R] q (1, 0)) + b • (1 ⊗ₜ[R] q (0, 1)) := by
  induction z using TensorProduct.inductionOn with
  | tmul s x =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hq x
    refine ⟨s * algebraMap R S a, s * algebraMap R S b, ?_⟩
    rw [pair_decomposition, TensorProduct.tmul_add]
    simp [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_comm]
  | add x y hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, d, rfl⟩ := hy
    exact ⟨a + c, b + d, by simp only [add_smul]; abel⟩

/-- Surjectivity, not a chosen coprime pair, proves the framed coordinates coprime. -/
theorem frame_coordinates_coprime (q : R × R →ₗ[R] Q) (hq : Function.Surjective q)
    (frame : (S ⊗[R] Q) ≃ₗ[S] S) :
    IsCoprime (frame (1 ⊗ₜ[R] q (1, 0))) (frame (1 ⊗ₜ[R] q (0, 1))) := by
  obtain ⟨a, b, he⟩ := extended_pair_generates q hq (frame.symm 1)
  refine ⟨a, b, ?_⟩
  have h := congrArg frame he
  simpa only [LinearEquiv.apply_symm_apply, map_add, map_smul, smul_eq_mul] using h.symm

variable [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- Extend a quotient frame along a coefficient map, on the tensor module. -/
def extendFrame (frame : (S ⊗[R] Q) ≃ₗ[S] S) : (T ⊗[R] Q) ≃ₗ[T] T :=
  (AlgebraTensorModule.cancelBaseChange R S T T Q).symm ≪≫ₗ
    frame.baseChange S T (S ⊗[R] Q) S ≪≫ₗ AlgebraTensorModule.rid S T T

@[simp] theorem extendFrame_one_tmul (frame : (S ⊗[R] Q) ≃ₗ[S] S) (x : Q) :
    extendFrame frame (1 ⊗ₜ[R] x) = algebraMap S T (frame (1 ⊗ₜ[R] x)) := by
  simp [extendFrame, Algebra.smul_def]

/-- Two extended local frames automatically give a common unit on both ordered coordinates. -/
theorem extended_frames_common_unit
    (frame : (S ⊗[R] Q) ≃ₗ[S] S) (frame' : (T ⊗[R] Q) ≃ₗ[T] T) (x y : Q) :
    ∃ u : Tˣ,
      frame' (1 ⊗ₜ[R] x) = (u : T) * algebraMap S T (frame (1 ⊗ₜ[R] x)) ∧
      frame' (1 ⊗ₜ[R] y) = (u : T) * algebraMap S T (frame (1 ⊗ₜ[R] y)) := by
  simpa only [extendFrame_one_tmul] using
    quotient_frame_change_pair (extendFrame frame) frame' (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y)

end FlagVarieties.Foundations.QuotientPair
