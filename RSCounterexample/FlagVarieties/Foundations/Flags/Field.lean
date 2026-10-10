import RSCounterexample.FlagVarieties.Foundations.Geometry.CompleteFlag
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.Preorder.Finite

/-!
# Dimensions and coordinate transport for complete flags over a field

All flags in this file are `Geometry.CompleteFlag`.
Transport to an arbitrary linearly equivalent module acts on its
subspaces; no additional flag type is introduced.
-/

namespace FlagVarieties.Foundations.FieldFlags

open Schubert.Geometry
open Module

universe u v w

variable {K : Type u} [DivisionRing K] {n : ℕ}

/-- The covering conditions make the indexed chain strictly increasing. -/
theorem step_strictMono (F : CompleteFlag K n) : StrictMono F.step :=
  Fin.strictMono_iff_lt_succ.mpr fun i => (F.step_covBy i).lt

/-- The dimension of step `j` is its flag index. -/
theorem step_finrank (F : CompleteFlag K n) (j : Fin (n + 1)) :
    finrank K (F.step j) = j.val := by
  let rankIndex : Fin (n + 1) → Fin (n + 1) := fun i =>
    ⟨finrank K (F.step i), Nat.lt_succ_of_le (by
      simpa only [CoordinateSpace, Module.finrank_pi, Fintype.card_fin] using
        (F.step i).finrank_le)⟩
  have hstrict : StrictMono rankIndex := fun _ _ hij =>
    Submodule.finrank_lt_finrank_of_lt (step_strictMono F hij)
  exact congrArg Fin.val (hstrict.apply_eq (x := j))

variable {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]

/-- A step of an existing flag, expressed in coordinates supplied by `e`. -/
def transportStep (F : CompleteFlag K n)
    (e : CoordinateSpace K n ≃ₗ[K] V) (j : Fin (n + 1)) : Submodule K V :=
  (F.step j).map e.toLinearMap

@[simp] theorem transportStep_zero (F : CompleteFlag K n)
    (e : CoordinateSpace K n ≃ₗ[K] V) : transportStep F e 0 = ⊥ := by
  simp [transportStep, F.step_zero]

@[simp] theorem transportStep_last (F : CompleteFlag K n)
    (e : CoordinateSpace K n ≃ₗ[K] V) : transportStep F e (Fin.last n) = ⊤ := by
  change (Submodule.orderIsoMapComap e) (F.step (Fin.last n)) = ⊤
  rw [F.step_last, (Submodule.orderIsoMapComap e).map_top]

theorem transportStep_covBy (F : CompleteFlag K n)
    (e : CoordinateSpace K n ≃ₗ[K] V) (i : Fin n) :
    transportStep F e i.castSucc ⋖ transportStep F e i.succ :=
  Submodule.map_covBy_of_injective e.injective (F.step_covBy i)

theorem transportStep_finrank (F : CompleteFlag K n)
    (e : CoordinateSpace K n ≃ₗ[K] V) (j : Fin (n + 1)) :
    finrank K (transportStep F e j) = j.val := by
  unfold transportStep
  rw [← (e.submoduleMap (F.step j)).finrank_eq]
  exact step_finrank F j

@[simp] theorem transportStep_refl (F : CompleteFlag K n) (j : Fin (n + 1)) :
    transportStep F (LinearEquiv.refl K (CoordinateSpace K n)) j = F.step j := by
  simp [transportStep]

/-- Coordinate changes compose on the subspaces. -/
theorem transportStep_trans (F : CompleteFlag K n)
    (e : CoordinateSpace K n ≃ₗ[K] V) (f : V ≃ₗ[K] W) (j : Fin (n + 1)) :
    transportStep F (e.trans f) j = (transportStep F e j).map f.toLinearMap := by
  exact Submodule.map_comp e.toLinearMap f.toLinearMap (F.step j)

/-- Transport along an equivalence of the coordinate vector space. -/
def transport (F : CompleteFlag K n)
    (e : CoordinateSpace K n ≃ₗ[K] CoordinateSpace K n) : CompleteFlag K n where
  step := transportStep F e
  step_zero := transportStep_zero F e
  step_last := transportStep_last F e
  step_covBy := transportStep_covBy F e

@[simp] theorem transport_step (F : CompleteFlag K n)
    (e : CoordinateSpace K n ≃ₗ[K] CoordinateSpace K n) (j : Fin (n + 1)) :
    (transport F e).step j = (F.step j).map e.toLinearMap := rfl

/-- Extensionality for the existing structure, without adding a flag wrapper. -/
theorem flag_ext {F G : CompleteFlag K n} (h : F.step = G.step) : F = G := by
  cases F
  cases G
  cases h
  rfl

@[simp] theorem transport_refl (F : CompleteFlag K n) :
    transport F (LinearEquiv.refl K (CoordinateSpace K n)) = F := by
  apply flag_ext
  funext j
  exact transportStep_refl F j

theorem transport_trans (F : CompleteFlag K n)
    (e f : CoordinateSpace K n ≃ₗ[K] CoordinateSpace K n) :
    transport (transport F e) f = transport F (e.trans f) := by
  apply flag_ext
  funext j
  exact (transportStep_trans F e f j).symm

@[simp] theorem transport_symm (F : CompleteFlag K n)
    (e : CoordinateSpace K n ≃ₗ[K] CoordinateSpace K n) :
    transport (transport F e) e.symm = F := by
  rw [transport_trans, e.self_trans_symm, transport_refl]

/-- The quotient dimension after coordinate transport. -/
theorem transportStep_quotient_finrank (F : CompleteFlag K n)
    (e : CoordinateSpace K n ≃ₗ[K] V) (j : Fin (n + 1)) :
    finrank K (V ⧸ transportStep F e j) = n - j.val := by
  let : FiniteDimensional K V := Module.Finite.equiv e
  rw [Submodule.finrank_quotient, transportStep_finrank, ← e.finrank_eq]
  simp only [CoordinateSpace, Module.finrank_pi, Fintype.card_fin]

/-- The quotient by the penultimate step is one-dimensional. -/
theorem penultimate_quotient_finrank (F : CompleteFlag K (n + 1))
    (e : CoordinateSpace K (n + 1) ≃ₗ[K] V) :
    finrank K (V ⧸ transportStep F e (Fin.last n).castSucc) = 1 := by
  rw [transportStep_quotient_finrank]
  simp

/-- A choice of linear coordinate on the final one-dimensional quotient.
This is an existence choice, not a canonical quotient frame. -/
noncomputable def penultimateQuotientEquiv (F : CompleteFlag K (n + 1))
    (e : CoordinateSpace K (n + 1) ≃ₗ[K] V) :
    (V ⧸ transportStep F e (Fin.last n).castSucc) ≃ₗ[K] K :=
  (Module.nonempty_linearEquiv_of_finrank_eq_one (penultimate_quotient_finrank F e)).some.symm

end FlagVarieties.Foundations.FieldFlags
