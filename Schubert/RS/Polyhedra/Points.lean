import Schubert.RS.Polyhedra.IntPolyhedron
import Schubert.RS.Polyhedra.FourierMotzkin
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Points of a system of integer linear inequalities

For a system `P : IntPolyhedron` of inequalities `a · x ≤ β` with integer data: its solution sets
over an ordered field and over `ℤ`, and the scaling of its right-hand sides.

## Main definitions

* `Schubert.RS.IntPolyhedron.points`: the solutions over a linearly ordered field.
* `Schubert.RS.IntPolyhedron.intPoints`: the integer solutions.
* `Schubert.RS.IntPolyhedron.scaleRhs`: the system `a · x ≤ N β`.

## Main results

* `Schubert.RS.IntPolyhedron.points_nonempty_congr`: a real solution exists iff a rational one
  does (Fourier–Motzkin).
* `Schubert.RS.IntPolyhedron.exists_intPoint_scaleRhs`: a rational solution gives an integer
  solution of `a · x ≤ N β` for some `N ≥ 1`.
-/

namespace Schubert.RS

namespace IntPolyhedron

variable (P : IntPolyhedron) (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The solutions of the system over `K`. -/
def points : Set (Fin P.dim → K) := {x | P.Satisfies x}

/-- The integer solutions of the system. -/
def intPoints : Set (Fin P.dim → ℤ) :=
  {z | ∀ r ∈ P.rows, ∑ i : Fin P.dim, r.1.getD i 0 * z i ≤ r.2}

/-- The system as a list of rows with coefficient functions. -/
def toLinRows : LinRows P.dim := P.rows.map fun r => (fun i => r.1.getD i 0, r.2)

variable {P K}

omit [IsStrictOrderedRing K] in
theorem mem_points_iff_holds (x : Fin P.dim → K) : x ∈ P.points K ↔ P.toLinRows.Holds x := by
  simp only [points, Set.mem_ofPred_eq, Satisfies, rowValue, LinRows.Holds, toLinRows, List.mem_map]
  constructor
  · rintro h _ ⟨r, hr, rfl⟩
    exact h r hr
  · intro h r hr
    exact h _ ⟨r, hr, rfl⟩

/-- An integer point is a solution over every ordered field. -/
theorem mem_intPoints_iff_cast (z : Fin P.dim → ℤ) :
    z ∈ P.intPoints ↔ (fun i => (z i : K)) ∈ P.points K := by
  simp only [intPoints, points, Set.mem_ofPred_eq, Satisfies, rowValue]
  refine forall₂_congr fun r _ => ?_
  rw [← Int.cast_le (R := K)]
  push_cast
  rfl

omit [IsStrictOrderedRing K] in
theorem points_nonempty_iff_feasible : (P.points K).Nonempty ↔ P.toLinRows.Feasible K :=
  ⟨fun ⟨x, hx⟩ => ⟨x, (mem_points_iff_holds x).1 hx⟩,
    fun ⟨x, hx⟩ => ⟨x, (mem_points_iff_holds x).2 hx⟩⟩

/-- **Fourier–Motzkin**: the system has a solution over one linearly ordered field iff it has one
over another. -/
theorem points_nonempty_congr (L : Type*) [Field L] [LinearOrder L] [IsStrictOrderedRing L] :
    (P.points K).Nonempty ↔ (P.points L).Nonempty := by
  rw [points_nonempty_iff_feasible, points_nonempty_iff_feasible]
  exact LinRows.feasible_congr L _

/-- A real solution exists iff a rational one does. -/
theorem points_real_nonempty_iff_rat : (P.points ℝ).Nonempty ↔ (P.points ℚ).Nonempty :=
  points_nonempty_congr ℚ

theorem ratFeasible_iff : P.RatFeasible ↔ (P.points ℚ).Nonempty := Iff.rfl

/-! ### Scaling the right-hand sides -/

variable (P) in
/-- The system `a · x ≤ N β`. -/
def scaleRhs (N : ℕ) : IntPolyhedron where
  dim := P.dim
  rows := P.rows.map fun r => (r.1, N * r.2)

/-- **Clearing denominators**: a rational solution `x` gives the integer solution `N x` of
`a · x ≤ N β`, for `N` a common denominator. -/
theorem exists_intPoint_scaleRhs (h : (P.points ℚ).Nonempty) :
    ∃ N : ℕ, 0 < N ∧ (P.scaleRhs N).intPoints.Nonempty := by
  obtain ⟨x, hx⟩ := h
  set N : ℕ := ∏ i, (x i).den with hN
  have hNpos : 0 < N := Finset.prod_pos fun i _ => (x i).den_pos
  have hdvd : ∀ i, ((x i).den : ℤ) ∣ (N : ℤ) := fun i =>
    Int.natCast_dvd_natCast.mpr (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  let z : Fin P.dim → ℤ := fun i => (x i).num * ((N : ℤ) / (x i).den)
  have hz : ∀ i, (z i : ℚ) = N * x i := by
    intro i
    have hden : ((x i).den : ℚ) ≠ 0 := by exact_mod_cast (x i).den_ne_zero
    simp only [z, Int.cast_mul]
    rw [Int.cast_div (hdvd i) (by exact_mod_cast hden)]
    nth_rw 3 [← Rat.num_div_den (x i)]
    push_cast
    ring
  refine ⟨N, hNpos, z, ?_⟩
  simp only [intPoints, scaleRhs, List.mem_map, forall_exists_index, and_imp]
  rintro _ r hr rfl
  have h := hx r hr
  simp only [rowValue] at h
  rw [← Int.cast_le (R := ℚ)]
  push_cast
  simp only [hz]
  have hNq : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  calc ∑ i : Fin P.dim, (r.1.getD i 0 : ℚ) * (N * x i)
      = N * ∑ i : Fin P.dim, (r.1.getD i 0 : ℚ) * x i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ N * r.2 := mul_le_mul_of_nonneg_left h hNq

end IntPolyhedron

end Schubert.RS
