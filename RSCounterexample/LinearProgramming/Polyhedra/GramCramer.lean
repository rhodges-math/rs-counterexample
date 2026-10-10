import RSCounterexample.LinearProgramming.Polyhedra.SupportReduction
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Basic solutions of integer systems are small

Let `M w = c` be a system with integer data, and let `w` be a solution whose support columns are
linearly independent. Write `A` for the integer matrix of the support columns. The Gram matrix
`G = Aᵀ A` is then invertible (`LinearProgramming.gram_det_ne_zero`), and `w` solves
`G w = Aᵀ c` on its support. By Cramer's rule, every entry of `w` is a quotient `N / D` of integer
determinants: `D = det G` and `N` the determinant of `G` with one column replaced by `Aᵀ c`
(`LinearProgramming.exists_cramer_repr`). Both are bounded by `Matrix.det_le`, the bound
`|det| ≤ k! x^k` for `k × k` matrices with entries at most `x`.

Hence every basic solution has entries at most `B` and nonzero entries at least `1 / B`, where
`B = k! ((r + 1)(U + 1)²)^k` for `r` equations, `k` variables and integer data at most `U`
(`LinearProgramming.exists_small_basic_solution`).

## Main definitions

* `LinearProgramming.toQ M`: an integer matrix as a rational matrix.
* `LinearProgramming.basicBound r k U`: the bound `k! ((r + 1)(U + 1)²)^k`.

## Main results

* `LinearProgramming.gram_det_ne_zero`: the Gram matrix of linearly independent columns is
  invertible.
* `LinearProgramming.exists_cramer_repr`: the entries of a basic solution are quotients of
  bounded integers.
* `LinearProgramming.exists_small_basic_solution`: every nonnegative solution can be replaced by
  a small basic one with no larger nonnegative objective.
-/

namespace LinearProgramming

open Matrix

/-- An integer matrix as a rational matrix. -/
def toQ {ρ ι : Type*} (M : Matrix ρ ι ℤ) : Matrix ρ ι ℚ := M.map (Int.cast : ℤ → ℚ)

@[simp] theorem toQ_apply {ρ ι : Type*} (M : Matrix ρ ι ℤ) (i : ρ) (j : ι) :
    toQ M i j = M i j := rfl

/-- The bound `k! ((r + 1)(U + 1)²)^k` on the numerators and denominators of the basic solutions
of a system with `r` equations, `k` variables and integer data at most `U` in absolute value. -/
def basicBound (r k U : ℕ) : ℕ := k.factorial * ((r + 1) * (U + 1) ^ 2) ^ k

theorem one_le_basicBound (r k U : ℕ) : 1 ≤ basicBound r k U :=
  Nat.mul_le_mul (Nat.factorial_pos k) (Nat.one_le_pow _ _ (by positivity))

theorem basicBound_mono {r k k' U : ℕ} (hk : k ≤ k') : basicBound r k U ≤ basicBound r k' U :=
  Nat.mul_le_mul (Nat.factorial_le hk) (Nat.pow_le_pow_right (by positivity) hk)

/-! ### The Gram matrix -/

/-- **The Gram matrix of linearly independent columns is invertible.** -/
theorem gram_det_ne_zero {ρ S : Type*} [Fintype ρ] [Fintype S] [DecidableEq S]
    (A : Matrix ρ S ℚ) (hA : LinearIndependent ℚ fun j : S => fun i => A i j) :
    (Aᵀ * A).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hGv⟩ := exists_mulVec_eq_zero_iff.mpr h
  have hAv : A *ᵥ v = 0 := by
    have h1 : (A *ᵥ v) ⬝ᵥ (A *ᵥ v) = 0 := by
      have := congrArg (fun u => v ⬝ᵥ u) hGv
      simp only [dotProduct_zero] at this
      rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose] at this
      exact this
    exact dotProduct_self_eq_zero.mp h1
  apply hv
  have := Fintype.linearIndependent_iff.mp hA v (by
    funext i
    have := congrFun hAv i
    simpa [mulVec, dotProduct, mul_comm] using this)
  funext j
  exact this j

/-- The determinant of an integer matrix, computed over the rationals. -/
theorem det_map_intCast {S : Type*} [Fintype S] [DecidableEq S] (N : Matrix S S ℤ) :
    (N.map (Int.cast : ℤ → ℚ)).det = N.det := by
  have := (Int.castRingHom ℚ).map_det N
  rw [RingHom.mapMatrix_apply, Int.coe_castRingHom] at this
  exact this.symm

/-! ### Cramer's rule for basic solutions -/

variable {ρ ι : Type*} [Fintype ρ] [Fintype ι] [DecidableEq ι]

/-- **The entries of a basic solution are quotients of bounded integers.** If `w` solves the
integer system `M w = c` and its support columns are linearly independent, then there is a nonzero
integer `D` with `D w` integral, and `D` and the entries of `D w` are bounded by
`basicBound (#ρ) (#ι) U`, where `U` bounds the data. -/
theorem exists_cramer_repr (M : Matrix ρ ι ℤ) (c : ρ → ℤ) {U : ℕ} (hM : ∀ i j, |M i j| ≤ U)
    (hc : ∀ i, |c i| ≤ U) {w : ι → ℚ} (hMw : toQ M *ᵥ w = fun i => (c i : ℚ))
    (hind : IndepSupport (toQ M) w) :
    ∃ D : ℤ, D ≠ 0 ∧ |D| ≤ basicBound (Fintype.card ρ) (Fintype.card ι) U ∧
      ∀ j, ∃ N : ℤ, (D : ℚ) * w j = N ∧ |N| ≤ basicBound (Fintype.card ρ) (Fintype.card ι) U := by
  classical
  set S := {j // w j ≠ 0}
  -- the support columns, over the integers and over the rationals
  set AZ : Matrix ρ S ℤ := Matrix.of fun i j => M i j
  set A : Matrix ρ S ℚ := Matrix.of fun i j => (M i j : ℚ)
  set GZ : Matrix S S ℤ := AZᵀ * AZ
  set bZ : S → ℤ := AZᵀ *ᵥ c
  have hG : GZ.map (Int.cast : ℤ → ℚ) = Aᵀ * A := by
    ext a b
    simp only [GZ, AZ, A, map_apply, mul_apply, transpose_apply, of_apply]
    push_cast
    rfl
  have hb : (fun j => (bZ j : ℚ)) = Aᵀ *ᵥ fun i => (c i : ℚ) := by
    funext j
    simp only [bZ, A, AZ, mulVec, dotProduct, transpose_apply, of_apply]
    push_cast
    rfl
  -- the restriction of `w` solves the Gram system
  set wS : S → ℚ := fun j => w j
  have hAw : A *ᵥ wS = fun i => (c i : ℚ) := by
    rw [← hMw]
    funext i
    simp only [mulVec, dotProduct, toQ_apply, A, wS, of_apply]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun k => w k ≠ 0) (fun k => (M i k : ℚ) * w k)]
    have h2 : ∑ x : {k // ¬ (w k ≠ 0)}, (M i x : ℚ) * w x = 0 :=
      Finset.sum_eq_zero fun x _ => by
        have := x.2
        simp only [ne_eq, not_not] at this
        rw [this, mul_zero]
    rw [h2, add_zero]
  have hGw : (Aᵀ * A) *ᵥ wS = Aᵀ *ᵥ fun i => (c i : ℚ) := by
    rw [← mulVec_mulVec, hAw]
  have hdet : (Aᵀ * A).det ≠ 0 := gram_det_ne_zero A hind
  have hDZ : (GZ.det : ℚ) = (Aᵀ * A).det := by
    rw [← hG, det_map_intCast]
  -- Cramer's rule
  have hcramer : ∀ j : S, (GZ.det : ℚ) * w j = ((GZ.updateCol j bZ).det : ℚ) := by
    intro j
    have h1 : (Aᵀ * A).det • wS = cramer (Aᵀ * A) (Aᵀ *ᵥ fun i => (c i : ℚ)) := by
      rw [← hGw, cramer_eq_adjugate_mulVec, mulVec_mulVec, adjugate_mul, smul_mulVec,
        one_mulVec]
    have h2 := congrFun h1 j
    rw [Pi.smul_apply, smul_eq_mul, cramer_apply] at h2
    rw [hDZ, h2, ← hG, ← hb, ← det_map_intCast]
    congr 1
    ext a b
    simp only [map_apply, updateCol_apply]
    split <;> rfl
  -- bounds
  set x : ℤ := (Fintype.card ρ : ℤ) * U ^ 2 with hx
  have hxB : x ≤ ((Fintype.card ρ + 1) * (U + 1) ^ 2 : ℕ) := by
    push_cast
    have : (0 : ℤ) ≤ U := by positivity
    nlinarith
  have hGZ : ∀ a b, |GZ a b| ≤ x := by
    intro a b
    simp only [GZ, mul_apply, AZ, transpose_apply, of_apply]
    calc |∑ i, M i a * M i b| ≤ ∑ i, |M i a * M i b| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : ρ, (U : ℤ) ^ 2 := Finset.sum_le_sum fun i _ => by
          rw [abs_mul, sq]
          exact mul_le_mul (hM i a) (hM i b) (abs_nonneg _) (by positivity)
      _ = x := by simp [hx]
  have hbZ : ∀ a, |bZ a| ≤ x := by
    intro a
    simp only [bZ, mulVec, dotProduct, AZ, transpose_apply, of_apply]
    calc |∑ i, M i a * c i| ≤ ∑ i, |M i a * c i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : ρ, (U : ℤ) ^ 2 := Finset.sum_le_sum fun i _ => by
          rw [abs_mul, sq]
          exact mul_le_mul (hM i a) (hc i) (abs_nonneg _) (by positivity)
      _ = x := by simp [hx]
  have hcard : Fintype.card S ≤ Fintype.card ι := Fintype.card_subtype_le _
  have hdetle : ∀ N : Matrix S S ℤ, (∀ a b, |N a b| ≤ x) →
      |N.det| ≤ basicBound (Fintype.card ρ) (Fintype.card ι) U := by
    intro N hN
    have h1 := det_le (abv := AbsoluteValue.abs) (x := x) hN
    simp only [AbsoluteValue.abs_apply, nsmul_eq_mul] at h1
    have h2 : ((Fintype.card S).factorial : ℤ) * x ^ Fintype.card S ≤
        basicBound (Fintype.card ρ) (Fintype.card S) U := by
      simp only [basicBound]
      push_cast
      have hx0 : 0 ≤ x := by positivity
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 (by exact_mod_cast hxB) _)
        (by positivity)
    have h3 : (basicBound (Fintype.card ρ) (Fintype.card S) U : ℤ) ≤
        basicBound (Fintype.card ρ) (Fintype.card ι) U := by
      exact_mod_cast basicBound_mono hcard
    linarith
  refine ⟨GZ.det, fun h0 => hdet (by rw [← hDZ, h0, Int.cast_zero]), hdetle GZ hGZ, fun j => ?_⟩
  by_cases hj : w j = 0
  · exact ⟨0, by simp [hj], by simp⟩
  · refine ⟨(GZ.updateCol ⟨j, hj⟩ bZ).det, hcramer ⟨j, hj⟩, hdetle _ fun a b => ?_⟩
    simp only [updateCol_apply]
    split
    · exact hbZ a
    · exact hGZ a b

/-- An entry `N / D` of a basic solution is at most `B` when `|N| ≤ B`. -/
theorem abs_le_of_cramer {D N : ℤ} {B : ℕ} {y : ℚ} (hD : D ≠ 0) (h : (D : ℚ) * y = N)
    (hN : |N| ≤ B) : |y| ≤ B := by
  have hD1 : (1 : ℚ) ≤ |(D : ℚ)| := by
    have : (1 : ℤ) ≤ |D| := Int.one_le_abs hD
    exact_mod_cast this
  have h1 : |(D : ℚ)| * |y| = |(N : ℚ)| := by rw [← abs_mul, h]
  have hN' : |(N : ℚ)| ≤ B := by exact_mod_cast hN
  nlinarith [abs_nonneg y]

/-- A nonzero entry `N / D` of a basic solution is at least `1 / B` when `|D| ≤ B`. -/
theorem one_div_le_of_cramer {D N : ℤ} {B : ℕ} {y : ℚ} (hD0 : D ≠ 0) (h : (D : ℚ) * y = N)
    (hDB : |D| ≤ B) (hy : y ≠ 0) : 1 / (B : ℚ) ≤ |y| := by
  have hN : N ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero, mul_eq_zero] at h
    rcases h with hD | hy'
    · exact hD0 (by exact_mod_cast hD)
    · exact hy hy'
  have hN1 : (1 : ℚ) ≤ |(N : ℚ)| := by
    have : (1 : ℤ) ≤ |N| := Int.one_le_abs hN
    exact_mod_cast this
  have hB : (0 : ℚ) < B := by
    have : (1 : ℤ) ≤ |D| := Int.one_le_abs hD0
    have : (1 : ℤ) ≤ B := le_trans this hDB
    exact_mod_cast this
  have hDB' : |(D : ℚ)| ≤ B := by exact_mod_cast hDB
  have h1 : |(D : ℚ)| * |y| = |(N : ℚ)| := by rw [← abs_mul, h]
  rw [div_le_iff₀ hB]
  nlinarith [abs_nonneg y, abs_nonneg (D : ℚ)]

/-- **Small basic solutions.** Every nonnegative solution of an integer system `M w = c` with
data at most `U` can be replaced by a nonnegative solution with no larger nonnegative objective
`f`, all of whose entries are at most `B` and whose nonzero entries are at least `1 / B`, where
`B = basicBound (#ρ) (#ι) U`. -/
theorem exists_small_basic_solution (M : Matrix ρ ι ℤ) (c : ρ → ℤ) {U : ℕ}
    (hM : ∀ i j, |M i j| ≤ U) (hc : ∀ i, |c i| ≤ U) {f : ι → ℚ} (hf : ∀ j, 0 ≤ f j)
    {w : ι → ℚ} (hw : ∀ j, 0 ≤ w j) (hMw : toQ M *ᵥ w = fun i => (c i : ℚ)) :
    ∃ w' : ι → ℚ, (∀ j, 0 ≤ w' j) ∧ toQ M *ᵥ w' = (fun i => (c i : ℚ)) ∧
      f ⬝ᵥ w' ≤ f ⬝ᵥ w ∧
      (∀ j, w' j ≤ basicBound (Fintype.card ρ) (Fintype.card ι) U) ∧
      ∀ j, w' j ≠ 0 → 1 / (basicBound (Fintype.card ρ) (Fintype.card ι) U : ℚ) ≤ w' j := by
  obtain ⟨w', hw', hMw', hfw', hind⟩ := exists_indepSupport (toQ M) _ hf hw hMw
  obtain ⟨D, hD, hDB, hN⟩ := exists_cramer_repr M c hM hc hMw' hind
  refine ⟨w', hw', hMw', hfw', fun j => ?_, fun j hj => ?_⟩
  · obtain ⟨N, hDN, hNB⟩ := hN j
    exact le_trans (le_abs_self _) (abs_le_of_cramer hD hDN hNB)
  · obtain ⟨N, hDN, _⟩ := hN j
    have := one_div_le_of_cramer hD hDN hDB hj
    rwa [abs_of_nonneg (hw' j)] at this

end LinearProgramming
