import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.Data.Int.Cast.Field
import Mathlib.Tactic.FieldSimp

/-!
# Fraction-free Gaussian elimination

Bareiss's fraction-free elimination without pivoting (`LinearProgramming.bareiss`) replaces, at
step `k`, every entry `(i, j)` with `i, j > k` by
`(H k k * H i j - H i k * H k j) / p`, where `p` is the pivot of the previous step (`1` at the
first step). If the leading principal minors used as divisors are nonzero, then after `k` steps
the entry `(i, j)` with `i, j ≥ k` is the bordered minor of the original matrix on the rows
`0, …, k - 1, i` and the columns `0, …, k - 1, j`, and the last pivot is the leading principal
minor of order `k` (`LinearProgramming.bareiss_eq_borderedMinor`). Over the integers every
division is exact, so the integer algorithm computes these minors
(`LinearProgramming.bareiss_int_eq_borderedMinor`). Their size is bounded by `Matrix.det_le`.

The proof avoids Sylvester's identity. One step of ordinary Gaussian elimination multiplies the
determinant by the pivot and passes to the Schur complement of the corner entry
(`LinearProgramming.det_eq_mul_det_schur`). Bordered minors behave the same way
(`LinearProgramming.borderedMinor_succ`), and so do the Bareiss states
(`LinearProgramming.bareiss_succ_schur`). Induction on the number of steps finishes.

Reference: E. H. Bareiss, *Sylvester's identity and multistep integer-preserving Gaussian
elimination*, Math. Comp. 22 (1968).

## Main definitions

* `LinearProgramming.bareiss H k`: the matrix and the last pivot after `k` steps.
* `LinearProgramming.borderedMinor H k i j`, `LinearProgramming.leadMinor H k`.

## Main results

* `LinearProgramming.det_eq_mul_det_schur`: the determinant and the Schur complement of a corner.
* `LinearProgramming.bareiss_eq_borderedMinor`: the invariant over a field.
* `LinearProgramming.bareiss_int_eq_borderedMinor`: the invariant over the integers.
* `LinearProgramming.abs_borderedMinor_le`: the size of the entries.
-/

namespace LinearProgramming

open Matrix

/-! ### The Schur complement of a corner entry -/

section Schur

variable {K : Type*} [Field K]

/-- **One step of Gaussian elimination.** The determinant of a matrix with a nonzero corner entry
is the corner entry times the determinant of the Schur complement of the corner. -/
theorem det_eq_mul_det_schur {k : ℕ} (B : Matrix (Fin (k + 1)) (Fin (k + 1)) K)
    (h : B 0 0 ≠ 0) :
    B.det = B 0 0 * (Matrix.of fun a b : Fin k =>
      B a.succ b.succ - B a.succ 0 * B 0 b.succ / B 0 0).det := by
  classical
  let L : Matrix (Fin (k + 1)) (Fin (k + 1)) K := Matrix.of fun a b =>
    if a = b then 1 else if b = 0 then -(B a 0 / B 0 0) else 0
  have hL : L.det = 1 := by
    rw [det_of_isLowerTriangular L fun a b hab => ?_]
    · simp [L]
    · have hab' : a < b := hab
      simp only [L, of_apply, ite_eq_right (ne_of_lt hab'), ite_eq_right (Fin.pos_iff_ne_zero.mp
        (lt_of_le_of_lt (Fin.zero_le a) hab'))]
  have hLB : ∀ (a : Fin k) (b : Fin (k + 1)),
      (L * B) a.succ b = B a.succ b - B a.succ 0 / B 0 0 * B 0 b := by
    intro a b
    rw [mul_apply, Fin.sum_univ_succ]
    simp only [L, of_apply, Fin.succ_ne_zero, ite_false, ite_true, neg_mul, Fin.succ_inj]
    rw [Finset.sum_eq_single a (fun c _ hc => by simp [Ne.symm hc]) (by simp)]
    simp only [ite_true, one_mul]
    ring
  have hL0 : ∀ b : Fin (k + 1), (L * B) 0 b = B 0 b := by
    intro b
    rw [mul_apply, Fin.sum_univ_succ]
    simp [L, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]
  rw [← one_mul B.det, ← hL, ← det_mul, det_succ_column_zero, Fin.sum_univ_succ]
  have hcol : ∀ a : Fin k, (L * B) a.succ 0 = 0 := fun a => by
    rw [hLB]
    field_simp
    ring
  simp only [hcol, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero,
    one_mul, hL0, Fin.succAbove_zero]
  congr 2
  ext a b
  simp only [submatrix_apply, of_apply, hLB]
  ring

end Schur

/-! ### Bordered minors -/

/-- The row or column index `a` of a bordered minor: `0, …, k - 1`, and then `i`. -/
def bord (k i : ℕ) (a : Fin (k + 1)) : ℕ := if (a : ℕ) < k then a else i

/-- The bordered minor of `H`: the determinant on the rows `0, …, k - 1, i` and the columns
`0, …, k - 1, j`. -/
def borderedMinor {R : Type*} [CommRing R] (H : ℕ → ℕ → R) (k i j : ℕ) : R :=
  (Matrix.of fun a b : Fin (k + 1) => H (bord k i a) (bord k j b)).det

/-- The leading principal minor of order `k`. -/
def leadMinor {R : Type*} [CommRing R] (H : ℕ → ℕ → R) (k : ℕ) : R :=
  (Matrix.of fun a b : Fin k => H a b).det

/-- The Schur complement of the corner entry, as a matrix indexed by natural numbers. -/
def schur {K : Type*} [Field K] (H : ℕ → ℕ → K) : ℕ → ℕ → K :=
  fun i j => H (i + 1) (j + 1) - H (i + 1) 0 * H 0 (j + 1) / H 0 0

theorem bord_succ (k i : ℕ) (a : Fin (k + 1)) : bord (k + 1) (i + 1) a.succ = bord k i a + 1 := by
  simp only [bord, Fin.val_succ]
  split_ifs <;> omega

theorem bord_zero (k i : ℕ) : bord (k + 1) i 0 = 0 := by
  simp [bord]

theorem borderedMinor_zero {R : Type*} [CommRing R] (H : ℕ → ℕ → R) (i j : ℕ) :
    borderedMinor H 0 i j = H i j := by
  simp [borderedMinor, bord]

theorem borderedMinor_one {R : Type*} [CommRing R] (H : ℕ → ℕ → R) (i j : ℕ) :
    borderedMinor H 1 i j = H 0 0 * H i j - H i 0 * H 0 j := by
  simp [borderedMinor, bord, det_fin_two]
  ring

theorem leadMinor_zero {R : Type*} [CommRing R] (H : ℕ → ℕ → R) : leadMinor H 0 = 1 := by
  simp [leadMinor]

theorem leadMinor_one {R : Type*} [CommRing R] (H : ℕ → ℕ → R) : leadMinor H 1 = H 0 0 := by
  simp [leadMinor]

theorem borderedMinor_self {R : Type*} [CommRing R] (H : ℕ → ℕ → R) (k : ℕ) :
    borderedMinor H k k k = leadMinor H (k + 1) := by
  unfold borderedMinor leadMinor
  congr 1
  ext a b
  simp only [of_apply, bord]
  congr 1 <;> split_ifs <;> omega

theorem leadMinor_succ {K : Type*} [Field K] (H : ℕ → ℕ → K) (h : H 0 0 ≠ 0) (k : ℕ) :
    leadMinor H (k + 1) = H 0 0 * leadMinor (schur H) k := by
  rw [leadMinor, det_eq_mul_det_schur _ (by simpa using h)]
  simp only [of_apply, Fin.val_zero, Fin.val_succ]
  rfl

theorem borderedMinor_succ {K : Type*} [Field K] (H : ℕ → ℕ → K) (h : H 0 0 ≠ 0) (k i j : ℕ) :
    borderedMinor H (k + 1) (i + 1) (j + 1) = H 0 0 * borderedMinor (schur H) k i j := by
  rw [borderedMinor, det_eq_mul_det_schur _ (by simpa [bord_zero] using h)]
  simp only [of_apply, bord_zero, bord_succ]
  rfl

/-! ### Bareiss elimination -/

/-- Step `k` of fraction-free elimination with previous pivot `p`: the entries `(i, j)` with
`i, j > k` become `(M k k * M i j - M i k * M k j) / p`. -/
def bareissStep {R : Type*} [CommRing R] [Div R] (k : ℕ) (p : R) (M : ℕ → ℕ → R) :
    ℕ → ℕ → R :=
  fun i j => if k < i ∧ k < j then (M k k * M i j - M i k * M k j) / p else M i j

/-- The matrix and the last pivot after `k` steps of fraction-free elimination without
pivoting. -/
def bareiss {R : Type*} [CommRing R] [Div R] (H : ℕ → ℕ → R) : ℕ → (ℕ → ℕ → R) × R
  | 0 => (H, 1)
  | k + 1 => (bareissStep k (bareiss H k).2 (bareiss H k).1, (bareiss H k).1 k k)

/-- Step `k` leaves the entries `(i, j)` with `i ≤ k` or `j ≤ k` unchanged. -/
theorem bareissStep_of_le {R : Type*} [CommRing R] [Div R] {k i j : ℕ} (p : R) (M : ℕ → ℕ → R)
    (h : i ≤ k ∨ j ≤ k) : bareissStep k p M i j = M i j := by
  unfold bareissStep
  rw [ite_eq_right (by omega)]

/-- The divisor of step `k`, read from the matrix: `1` at the first step, and otherwise the
diagonal entry `(k - 1, k - 1)`, which no later step changes. -/
def prevPivot {R : Type*} [CommRing R] (M : ℕ → ℕ → R) (k : ℕ) : R :=
  if k = 0 then 1 else M (k - 1) (k - 1)

/-- The last pivot is the diagonal entry it was read from. -/
theorem bareiss_snd {R : Type*} [CommRing R] [Div R] (H : ℕ → ℕ → R) (k : ℕ) :
    (bareiss H k).2 = prevPivot (bareiss H k).1 k := by
  cases k with
  | zero => simp [bareiss, prevPivot]
  | succ k =>
    simp only [prevPivot, Nat.add_sub_cancel, Nat.succ_ne_zero, ite_false]
    show (bareiss H k).1 k k = bareissStep k _ _ k k
    rw [bareissStep_of_le _ _ (Or.inl le_rfl)]

/-- Fraction-free elimination as a loop on matrices alone. -/
theorem bareiss_fst_succ {R : Type*} [CommRing R] [Div R] (H : ℕ → ℕ → R) (k : ℕ) :
    (bareiss H (k + 1)).1 = bareissStep k (prevPivot (bareiss H k).1 k) (bareiss H k).1 := by
  rw [← bareiss_snd]
  rfl

/-- **Bareiss states pass to the Schur complement.** After `k + 1` steps, the entries with both
indices positive and the pivot are the corner entry times those of the Schur complement after
`k` steps. -/
theorem bareiss_succ_schur {K : Type*} [Field K] (H : ℕ → ℕ → K) (h : H 0 0 ≠ 0) :
    ∀ k, (∀ i j, (bareiss H (k + 1)).1 (i + 1) (j + 1) = H 0 0 * (bareiss (schur H) k).1 i j) ∧
      (bareiss H (k + 1)).2 = H 0 0 * (bareiss (schur H) k).2
  | 0 => by
    refine ⟨fun i j => ?_, by simp [bareiss]⟩
    simp only [bareiss, bareissStep, Nat.zero_lt_succ, and_self, ite_true, div_one, schur]
    field_simp
  | k + 1 => by
    obtain ⟨ih1, ih2⟩ := bareiss_succ_schur H h k
    refine ⟨fun i j => ?_, ?_⟩
    · show bareissStep (k + 1) _ _ (i + 1) (j + 1) = H 0 0 * bareissStep k _ _ i j
      unfold bareissStep
      simp only [Nat.add_lt_add_iff_right]
      split_ifs
      · rw [ih1, ih1, ih1, ih1, ih2]
        by_cases hp : (bareiss (schur H) k).2 = 0
        · simp [hp]
        · field_simp
      · exact ih1 i j
    · exact ih1 k k

/-- **The Bareiss invariant over a field.** If the leading principal minors of orders `1, …,
k - 1` are nonzero, then after `k` steps the entry `(i, j)` with `i, j ≥ k` is the bordered minor
on the rows `0, …, k - 1, i` and the columns `0, …, k - 1, j`, and the last pivot is the leading
principal minor of order `k`. -/
theorem bareiss_eq_borderedMinor {K : Type*} [Field K] :
    ∀ (k : ℕ) (H : ℕ → ℕ → K), (∀ l, 1 ≤ l → l < k → leadMinor H l ≠ 0) →
      (∀ i j, k ≤ i → k ≤ j → (bareiss H k).1 i j = borderedMinor H k i j) ∧
        (bareiss H k).2 = leadMinor H k
  | 0, H, _ => ⟨fun i j _ _ => by simp [bareiss, borderedMinor_zero], by
      simp [bareiss, leadMinor_zero]⟩
  | 1, H, _ => by
    refine ⟨fun i j hi hj => ?_, by simp [bareiss, leadMinor_one]⟩
    simp only [bareiss, bareissStep, show 0 < i from hi, show 0 < j from hj, and_self, ite_true,
      div_one, borderedMinor_one]
  | k + 2, H, hlead => by
    have h0 : H 0 0 ≠ 0 := by
      have := hlead 1 le_rfl (by omega)
      rwa [leadMinor_one] at this
    have hlead' : ∀ l, 1 ≤ l → l < k + 1 → leadMinor (schur H) l ≠ 0 := fun l hl hlk => by
      have := hlead (l + 1) (by omega) (by omega)
      rw [leadMinor_succ H h0] at this
      exact right_ne_zero_of_mul this
    obtain ⟨ih1, ih2⟩ := bareiss_eq_borderedMinor (k + 1) (schur H) hlead'
    obtain ⟨hs1, hs2⟩ := bareiss_succ_schur H h0 (k + 1)
    refine ⟨fun i j hi hj => ?_, ?_⟩
    · obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [hs1, ih1 i j (by omega) (by omega), borderedMinor_succ H h0]
    · rw [hs2, ih2, leadMinor_succ H h0]

/-- The determinant of an integer matrix, computed over the rationals. -/
theorem det_intCast {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℤ) :
    ((A.det : ℤ) : ℚ) = (A.map (Int.cast : ℤ → ℚ)).det := by
  have := (Int.castRingHom ℚ).map_det A
  rwa [RingHom.mapMatrix_apply, Int.coe_castRingHom] at this

theorem borderedMinor_intCast (H : ℕ → ℕ → ℤ) (k i j : ℕ) :
    ((borderedMinor H k i j : ℤ) : ℚ) = borderedMinor (fun a b => (H a b : ℚ)) k i j := by
  rw [borderedMinor, det_intCast]
  rfl

theorem leadMinor_intCast (H : ℕ → ℕ → ℤ) (k : ℕ) :
    ((leadMinor H k : ℤ) : ℚ) = leadMinor (fun a b => (H a b : ℚ)) k := by
  rw [leadMinor, det_intCast]
  rfl

/-- **The Bareiss invariant over the integers.** If the leading principal minors of orders `1,
…, k - 1` are nonzero, every division is exact, and after `k` steps the entry `(i, j)` with
`i, j ≥ k` is the bordered minor and the last pivot is the leading principal minor of order
`k`. -/
theorem bareiss_int_eq_borderedMinor (H : ℕ → ℕ → ℤ) (k : ℕ)
    (hlead : ∀ l, 1 ≤ l → l < k → leadMinor H l ≠ 0) :
    (∀ i j, k ≤ i → k ≤ j → (bareiss H k).1 i j = borderedMinor H k i j) ∧
      (bareiss H k).2 = leadMinor H k := by
  set HQ : ℕ → ℕ → ℚ := fun a b => (H a b : ℚ)
  have hleadQ : ∀ l, 1 ≤ l → l < k → leadMinor HQ l ≠ 0 := fun l h1 h2 => by
    rw [← leadMinor_intCast]
    exact_mod_cast hlead l h1 h2
  -- the integer states are the casts of the rational ones, in the active range
  have key : ∀ k' ≤ k, (∀ i j, k' ≤ i → k' ≤ j →
      ((bareiss H k').1 i j : ℚ) = (bareiss HQ k').1 i j) ∧
      ((bareiss H k').2 : ℚ) = (bareiss HQ k').2 := by
    intro k' hk'
    induction k' with
    | zero => exact ⟨fun i j _ _ => rfl, by simp [bareiss]⟩
    | succ k' ih =>
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      refine ⟨fun i j hi hj => ?_, ih1 k' k' le_rfl le_rfl⟩
      show ((bareissStep k' _ _ i j : ℤ) : ℚ) = bareissStep k' _ _ i j
      unfold bareissStep
      rw [ite_eq_left ⟨by omega, by omega⟩, ite_eq_left ⟨by omega, by omega⟩]
      have hnum : ((((bareiss H k').1 k' k' * (bareiss H k').1 i j -
          (bareiss H k').1 i k' * (bareiss H k').1 k' j) : ℤ) : ℚ) =
          (bareiss HQ k').1 k' k' * (bareiss HQ k').1 i j -
            (bareiss HQ k').1 i k' * (bareiss HQ k').1 k' j := by
        push_cast
        rw [ih1 k' k' le_rfl le_rfl, ih1 i j (by omega) (by omega), ih1 i k' (by omega) le_rfl,
          ih1 k' j le_rfl (by omega)]
      -- the rational quotient is an integer bordered minor
      obtain ⟨hq1, hq2⟩ := bareiss_eq_borderedMinor k' HQ fun l h1 h2 => hleadQ l h1 (by omega)
      have hp : (bareiss HQ k').2 ≠ 0 := by
        rw [hq2]
        rcases Nat.eq_zero_or_pos k' with h0 | hpos
        · subst h0
          simp [leadMinor_zero]
        · exact hleadQ k' hpos (by omega)
      obtain ⟨hr1, _⟩ := bareiss_eq_borderedMinor (k' + 1) HQ fun l h1 h2 => hleadQ l h1 (by omega)
      have hval := hr1 i j hi hj
      simp only [bareiss, bareissStep, ite_eq_left (show k' < i ∧ k' < j from ⟨by omega, by omega⟩)]
        at hval
      rw [← borderedMinor_intCast] at hval
      set num := (bareiss H k').1 k' k' * (bareiss H k').1 i j -
        (bareiss H k').1 i k' * (bareiss H k').1 k' j
      have hpZ : ((bareiss H k').2 : ℚ) ≠ 0 := by rw [ih2]; exact hp
      have hdvd : (bareiss H k').2 ∣ num := by
        refine ⟨borderedMinor H (k' + 1) i j, ?_⟩
        have : (num : ℚ) = (bareiss H k').2 * borderedMinor H (k' + 1) i j := by
          rw [hnum, ← hval, ih2]
          field_simp
        exact_mod_cast this
      rw [Int.cast_div hdvd hpZ, hnum, ih2]
  obtain ⟨k1, k2⟩ := key k le_rfl
  obtain ⟨q1, q2⟩ := bareiss_eq_borderedMinor k HQ hleadQ
  refine ⟨fun i j hi hj => ?_, ?_⟩
  · have := k1 i j hi hj
    rw [q1 i j hi hj, ← borderedMinor_intCast] at this
    exact_mod_cast this
  · have := k2
    rw [q2, ← leadMinor_intCast] at this
    exact_mod_cast this

/-- **The numerators are exact multiples.** If the leading principal minors of orders `1, …, k`
are nonzero, the numerator of step `k` at `(i, j)` with `i, j > k` is the previous pivot times the
bordered minor of order `k + 2` on the rows `0, …, k, i` and the columns `0, …, k, j`. -/
theorem bareiss_int_num (H : ℕ → ℕ → ℤ) (k : ℕ) (hlead : ∀ l, 1 ≤ l → l ≤ k → leadMinor H l ≠ 0)
    {i j : ℕ} (hi : k < i) (hj : k < j) :
    (bareiss H k).1 k k * (bareiss H k).1 i j - (bareiss H k).1 i k * (bareiss H k).1 k j =
      (bareiss H k).2 * borderedMinor H (k + 1) i j := by
  set HQ : ℕ → ℕ → ℚ := fun a b => (H a b : ℚ)
  have hleadQ : ∀ l, 1 ≤ l → l ≤ k → leadMinor HQ l ≠ 0 := fun l h1 h2 => by
    rw [← leadMinor_intCast]
    exact_mod_cast hlead l h1 h2
  obtain ⟨z1, z2⟩ := bareiss_int_eq_borderedMinor H k fun l h1 h2 => hlead l h1 (by omega)
  obtain ⟨q1, q2⟩ := bareiss_eq_borderedMinor k HQ fun l h1 h2 => hleadQ l h1 (by omega)
  obtain ⟨r1, _⟩ := bareiss_eq_borderedMinor (k + 1) HQ fun l h1 h2 => hleadQ l h1 (by omega)
  have hval := r1 i j hi hj
  simp only [bareiss, bareissStep, ite_eq_left (show k < i ∧ k < j from ⟨hi, hj⟩)] at hval
  have hcast : ∀ a b, k ≤ a → k ≤ b → (bareiss HQ k).1 a b = (((bareiss H k).1 a b : ℤ) : ℚ) :=
    fun a b ha hb => by rw [q1 a b ha hb, z1 a b ha hb, borderedMinor_intCast]
  have hp : (bareiss HQ k).2 = (((bareiss H k).2 : ℤ) : ℚ) := by
    rw [q2, z2, leadMinor_intCast]
  have hp0 : (bareiss HQ k).2 ≠ 0 := by
    rw [q2]
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      simp [leadMinor_zero]
    · exact hleadQ k hpos le_rfl
  rw [hcast k k le_rfl le_rfl, hcast i j (by omega) (by omega), hcast i k (by omega) le_rfl,
    hcast k j le_rfl (by omega), ← borderedMinor_intCast, div_eq_iff hp0] at hval
  rw [hp] at hval
  exact_mod_cast hval.trans (mul_comm _ _)

/-- **The size of bordered minors**: at most `(k + 1)! U ^ (k + 1)` when the entries of `H` in
the rows and columns involved are at most `U`. -/
theorem abs_borderedMinor_le {H : ℕ → ℕ → ℤ} {U : ℤ} {n k i j : ℕ} (hk : k ≤ n) (hi : i < n)
    (hj : j < n) (hH : ∀ a < n, ∀ b < n, |H a b| ≤ U) :
    |borderedMinor H k i j| ≤ (k + 1).factorial * U ^ (k + 1) := by
  have h := det_le (abv := AbsoluteValue.abs)
    (A := Matrix.of fun a b : Fin (k + 1) => H (bord k i a) (bord k j b)) (x := U)
    fun a b => by
      simp only [AbsoluteValue.abs_apply, of_apply]
      refine hH _ ?_ _ ?_ <;> simp only [bord] <;> split_ifs <;> omega
  simpa [borderedMinor] using h

end LinearProgramming
