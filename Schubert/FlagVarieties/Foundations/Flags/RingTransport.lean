import Schubert.FlagVarieties.Foundations.Flags.Ring

/-!
# Coordinate transport of the existing ring flag

Each transported step is the image under a linear equivalence.
Its quotient is identified with the original quotient by Mathlib's
`Submodule.Quotient.equiv`; this preserves finite projectivity and stalk rank.
-/

namespace FlagVarieties.Foundations.RingFlag

universe u v w z

variable {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]
  {P : Type z} [AddCommGroup P] [Module R P] {n : ℕ}

/-- Transport an existing ring flag along a linear equivalence. -/
noncomputable def transport (F : RingFlag R M n) (e : M ≃ₗ[R] N) : RingFlag R N n where
  step j :=
    { toSubmodule := (F.step j).toSubmodule.map e.toLinearMap
      finite_quotient := Module.Finite.equiv (Submodule.Quotient.equiv _ _ e rfl)
      projective_quotient := Module.Projective.of_equiv (Submodule.Quotient.equiv _ _ e rfl)
      rankAtStalk_eq p := by
        have h := congrFun (Module.rankAtStalk_eq_of_equiv
          (Submodule.Quotient.equiv (F.step j).toSubmodule _ e rfl)) p
        exact h.symm.trans ((F.step j).rankAtStalk_eq p) }
  step_mono := fun _ _ hij => Submodule.map_mono (F.step_le_step hij)
  step_zero := by simp [F.step_zero]
  step_last := by
    change (Submodule.orderIsoMapComap e) (F.step (Fin.last n)).toSubmodule = ⊤
    rw [F.step_last, (Submodule.orderIsoMapComap e).map_top]

@[simp] theorem transport_step (F : RingFlag R M n) (e : M ≃ₗ[R] N) (j : Fin (n + 1)) :
    ((transport F e).step j).toSubmodule = (F.step j).toSubmodule.map e.toLinearMap := rfl

/-- The quotient comparison underlying coordinate transport: `e` induces
`M ⧸ Fⱼ ≃ N ⧸ e(Fⱼ)`, and `e(Fⱼ)` is step `j` of `transport F e` (`transport_step`). -/
noncomputable def transportQuotientEquiv (F : RingFlag R M n) (e : M ≃ₗ[R] N) (j : Fin (n + 1)) :
    (M ⧸ (F.step j).toSubmodule) ≃ₗ[R] (N ⧸ (F.step j).toSubmodule.map e.toLinearMap) :=
  Submodule.Quotient.equiv _ _ e rfl

@[simp] theorem transportQuotientEquiv_apply_mk
    (F : RingFlag R M n) (e : M ≃ₗ[R] N) (j : Fin (n + 1)) (x : M) :
    transportQuotientEquiv F e j (Submodule.Quotient.mk x) = Submodule.Quotient.mk (e x) := rfl

@[simp] theorem transport_refl (F : RingFlag R M n) :
    transport F (LinearEquiv.refl R M) = F := by
  apply RingFlag.ext
  intro j
  simp

theorem transport_trans (F : RingFlag R M n) (e : M ≃ₗ[R] N) (f : N ≃ₗ[R] P) :
    transport (transport F e) f = transport F (e.trans f) := by
  apply RingFlag.ext
  intro j
  exact (Submodule.map_comp e.toLinearMap f.toLinearMap (F.step j).toSubmodule).symm

@[simp] theorem transport_symm (F : RingFlag R M n) (e : M ≃ₗ[R] N) :
    transport (transport F e) e.symm = F := by
  rw [transport_trans, e.self_trans_symm, transport_refl]

theorem transport_injective (e : M ≃ₗ[R] N) :
    Function.Injective (fun F : RingFlag R M n => transport F e) := by
  intro F G h
  have h' := congrArg (fun H => transport H e.symm) h
  simpa only [transport_symm] using h'

section Field

open Schubert.Geometry

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

theorem transport_ofFieldFlag_step (F : CompleteFlag K n)
    (e : CoordinateSpace K n ≃ₗ[K] V) (j : Fin (n + 1)) :
    ((transport (ofFieldFlag F) e).step j).toSubmodule = FieldFlags.transportStep F e j := rfl

/-- Ring transport recovers the existing coordinate transport of field flags. -/
theorem toFieldFlag_transport (F : RingFlag K (CoordinateSpace K n) n)
    (e : CoordinateSpace K n ≃ₗ[K] CoordinateSpace K n) :
    toFieldFlag (transport F e) = FieldFlags.transport (toFieldFlag F) e := by
  apply FieldFlags.flag_ext
  rfl

theorem ofFieldFlag_transport (F : CompleteFlag K n)
    (e : CoordinateSpace K n ≃ₗ[K] CoordinateSpace K n) :
    ofFieldFlag (FieldFlags.transport F e) = transport (ofFieldFlag F) e := by
  apply RingFlag.ext
  intro j
  rfl

end Field
end FlagVarieties.Foundations.RingFlag
