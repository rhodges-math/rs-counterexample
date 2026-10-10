import RSCounterexample.FlagVarieties.Flag.Action
import RSCounterexample.FlagVarieties.Charts.AdaptedBasis

/-!
# The stabilizer of the standard flag

Over any commutative ring `A`, two invertible matrices `g, h` have the same image `g · E• = h · E•`
under the orbit map iff `g⁻¹ h` is upper triangular (`orbitMap_point_eq_iff`). In particular the
stabilizer of the standard flag is the upper triangular subgroup `B`, and the orbit map is
constant on right `B`-cosets.
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory
open Foundations Foundations.QuotientCharts

universe u

variable {A : Type u} [CommRing A] {n : ℕ}

theorem stdSpan_of_le {m : ℕ} (hm : n ≤ m) : stdSpan A n m = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [mem_stdSpan_iff]
  intro i hi
  exact absurd (lt_of_lt_of_le i.isLt hm) (not_lt.mpr hi)

theorem standardRingFlag_step_eq_stdSpan (j : Fin (n + 1)) :
    ((FlagScheme.standardRingFlag n A).step j).toSubmodule = stdSpan A n j.val :=
  FlagScheme.standardRingFlag_step A j

/-- The steps of `g · E•` are the images of the standard spans. -/
theorem transport_standardRingFlag_step (g : Matrix (Fin n) (Fin n) A) (hg : Invertible g)
    (j : Fin (n + 1)) :
    (((FlagScheme.standardRingFlag n A).transport (g.toLinearEquiv' hg)).step j).toSubmodule =
      (stdSpan A n j.val).map (Matrix.toLin' g) := by
  rw [RingFlag.transport_step, standardRingFlag_step_eq_stdSpan]
  rfl

/-- `g · E• = h · E•` iff `g⁻¹ h` is upper triangular. -/
theorem transport_standardRingFlag_eq_iff (g h : Matrix (Fin n) (Fin n) A) (hg : Invertible g)
    (hh : Invertible h) :
    (FlagScheme.standardRingFlag n A).transport (g.toLinearEquiv' hg) =
        (FlagScheme.standardRingFlag n A).transport (h.toLinearEquiv' hh) ↔
      (⅟g * h).BlockTriangular id := by
  rw [← map_stdSpan_eq_map_iff]
  constructor
  · intro e m
    by_cases hm : m ≤ n
    · have := congrArg (fun P : CoordinateFlag A n =>
        (P.step ⟨m, Nat.lt_succ_of_le hm⟩).toSubmodule) e
      simpa only [transport_standardRingFlag_step] using this
    · have hmn : stdSpan A n m = stdSpan A n n := by
        rw [stdSpan_of_le (le_of_lt (not_le.mp hm)), stdSpan_of_le le_rfl]
      have := congrArg (fun P : CoordinateFlag A n => (P.step (Fin.last n)).toSubmodule) e
      simp only [transport_standardRingFlag_step, Fin.val_last] at this
      rw [hmn]
      exact this
  · intro e
    apply RingFlag.ext
    intro j
    rw [transport_standardRingFlag_step, transport_standardRingFlag_step]
    exact e j.val

variable {R : Type u} [CommRing R] [Algebra R A]

/-- **Stabilizer of the standard flag.** Two points `g, h` of `GLₙ` have the same image under the
orbit map iff `g⁻¹ h` is upper triangular. -/
theorem orbitMap_point_eq_iff (k k' : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] A) :
    GLScheme.point R n k ≫ FlagScheme.orbitMap R n =
        GLScheme.point R n k' ≫ FlagScheme.orbitMap R n ↔
      ((GLScheme.pointMatrix R n k)⁻¹ * GLScheme.pointMatrix R n k').BlockTriangular id := by
  rw [FlagScheme.orbitMap_point, FlagScheme.orbitMap_point,
    (FlagScheme.ofRingFlag_injective (R := R)).eq_iff, GLScheme.pointEquiv, GLScheme.pointEquiv,
    transport_standardRingFlag_eq_iff, Matrix.invOf_eq_nonsing_inv]

/-- The orbit map is constant on right cosets of the upper triangular subgroup. -/
theorem orbitMap_point_eq_of_mul (k k' : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] A)
    (b : Matrix (Fin n) (Fin n) A) (hb : b.BlockTriangular id)
    (h : GLScheme.pointMatrix R n k' = GLScheme.pointMatrix R n k * b) :
    GLScheme.point R n k ≫ FlagScheme.orbitMap R n =
      GLScheme.point R n k' ≫ FlagScheme.orbitMap R n := by
  rw [orbitMap_point_eq_iff, h, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp
      (generalLinearMatrixAt_isUnit R A n k)), Matrix.one_mul]
  exact hb

end FlagVarieties
