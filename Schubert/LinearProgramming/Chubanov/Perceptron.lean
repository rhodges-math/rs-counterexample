import Schubert.LinearProgramming.Chubanov.Projection
import Schubert.LinearProgramming.Vectors.Search
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The counting perceptron and the cut

Let `P` be a symmetric matrix with diagonal entries at most `1`. The counting perceptron keeps
counts `c ∈ ℕᴺ`. While `P c` has an entry `≤ 0`, it adds `1` to the count of the least such
index `k`. Each step increases `q(c) = c · P c` by `2 (P c)_k + P k k ≤ 1`
(`LinearProgramming.perceptron_step`), so after `T` steps `q(c) ≤ T = ∑ c`. This is the
perceptron bound (Novikoff), the analysis of the basic procedure in Chubanov's algorithm
(S. Chubanov, *A polynomial projection algorithm for linear feasibility problems*, Math. Program.
153 (2015)) with the averaging step `y = c / T` in place of the von Neumann step. The counts stay
small integers, so no rounding is needed.

**The cut** (`LinearProgramming.cut`). If moreover `P` is idempotent, `q(c) ≤ T`, and `j` is an
index of the largest count, then every `x ∈ [0, 1]ᴺ` with `P x = x` has `x_j² T ≤ N³`. Indeed
`x_j c_j ≤ x · c = x · P c`, Cauchy–Schwarz bounds this by `(x · x)(P c · P c) ≤ N q(c)`, and
`c_j ≥ T / N`. So after `T ≥ 4 N³` steps without success, `x_j ≤ 1 / 2`.

The algorithm works with an integer matrix `Q = δ P`, `δ ≠ 0`: the tests are on the signs of
`δ (Q c)_i` (`LinearProgramming.perceptron`, `LinearProgramming.perceptron_spec`).

## Main definitions

* `LinearProgramming.percStep N Q δ`: one step of the counting perceptron on `Q`.
* `LinearProgramming.perceptron N Q δ T`: `T` steps from zero counts.

## Main results

* `LinearProgramming.perceptron_step`: the perceptron bound for one step.
* `LinearProgramming.perceptron_spec`: success gives `P c > 0`; failure gives `∑ c = T` and
  `c · P c ≤ T`.
* `LinearProgramming.cut`: the cut lemma.
-/

namespace LinearProgramming

open Matrix

variable {N : ℕ}

/-- The counts as a rational vector. -/
def countsQ (N : ℕ) (c : ℕ → ℕ) : Fin N → ℚ := fun j => (c j : ℚ)

/-- **The perceptron bound for one step.** For a symmetric `P` with `P k k ≤ 1` and
`(P c)_k ≤ 0`, adding `e_k` to `c` increases `c · P c` by at most `1`. -/
theorem perceptron_step {P : Matrix (Fin N) (Fin N) ℚ} (hs : Pᵀ = P) (hd : ∀ k, P k k ≤ 1)
    (c : Fin N → ℚ) (k : Fin N) (hk : (P *ᵥ c) k ≤ 0) :
    (c + Pi.single k 1) ⬝ᵥ (P *ᵥ (c + Pi.single k 1)) ≤ c ⬝ᵥ (P *ᵥ c) + 1 := by
  have h1 : Pi.single k 1 ⬝ᵥ (P *ᵥ c) = (P *ᵥ c) k := by
    rw [single_dotProduct, one_mul]
  have h2 : c ⬝ᵥ (P *ᵥ Pi.single k 1) = (P *ᵥ c) k := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hs, dotProduct_comm, single_dotProduct, one_mul]
  have h3 : Pi.single k 1 ⬝ᵥ (P *ᵥ Pi.single k 1) = P k k := by
    rw [single_dotProduct, one_mul, mulVec_single_one]
    rfl
  rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, h1, h2, h3]
  linarith [hd k]

/-! ### The counting perceptron on an integer matrix -/

/-- `(Q c)_i = ∑_{j < N} Q i j c j`. -/
def qmul (N : ℕ) (Q : ℕ → ℕ → ℤ) (c : ℕ → ℕ) (i : ℕ) : ℤ := ∑ j : Fin N, Q i j * (c j : ℤ)

/-- The index the perceptron increments: the least `k < N` with `δ (Q c)_k ≤ 0`. -/
def percIdx (N : ℕ) (Q : ℕ → ℕ → ℤ) (δ : ℤ) (c : ℕ → ℕ) : ℕ :=
  firstIdx (fun k => δ * qmul N Q c k ≤ 0) N

/-- **One step of the counting perceptron** on `Q` with scale `δ`. A finished state (flag `true`)
stays. Otherwise, if `δ (Q c)_i > 0` for all `i < N` the run succeeds; if not, the count of the
least index `k` with `δ (Q c)_k ≤ 0` grows by one. -/
def percStep (N : ℕ) (Q : ℕ → ℕ → ℤ) (δ : ℤ) (s : Bool × (ℕ → ℕ)) : Bool × (ℕ → ℕ) :=
  if s.1 = true then s
  else if ∀ i < N, 0 < δ * qmul N Q s.2 i then (true, s.2)
  else (false, fun l => if l = percIdx N Q δ s.2 then s.2 l + 1 else s.2 l)

/-- `T` steps of the counting perceptron from zero counts. -/
def perceptron (N : ℕ) (Q : ℕ → ℕ → ℤ) (δ : ℤ) (T : ℕ) : Bool × (ℕ → ℕ) :=
  loopN (fun _ => percStep N Q δ) T (false, fun _ => 0)

/-- **What the perceptron computes.** Let `Q = δ P` with `δ ≠ 0`, `P` symmetric with diagonal at
most `1`. After `T` steps either the run succeeded and `P c > 0`, or it failed, the counts sum
to `T`, and `c · P c ≤ T`. -/
theorem perceptron_spec {Q : ℕ → ℕ → ℤ} {δ : ℤ} {P : Matrix (Fin N) (Fin N) ℚ} (hδ : δ ≠ 0)
    (hQ : ∀ a b : Fin N, (Q a b : ℚ) = δ * P a b) (hs : Pᵀ = P) (hd : ∀ k, P k k ≤ 1) (T : ℕ) :
    ((perceptron N Q δ T).1 = true → ∀ i, 0 < (P *ᵥ countsQ N (perceptron N Q δ T).2) i) ∧
      ((perceptron N Q δ T).1 = false →
        ∑ j : Fin N, (perceptron N Q δ T).2 j = T ∧
        countsQ N (perceptron N Q δ T).2 ⬝ᵥ (P *ᵥ countsQ N (perceptron N Q δ T).2) ≤ T) := by
  -- `δ (Q c)_i` and `(P c)_i` have the same sign
  have hsign : ∀ (c : ℕ → ℕ) (i : Fin N),
      ((δ * qmul N Q c i : ℤ) : ℚ) = δ ^ 2 * (P *ᵥ countsQ N c) i := by
    intro c i
    simp only [qmul, mulVec, dotProduct, countsQ, Int.cast_mul, Int.cast_sum, Int.cast_natCast]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hQ]
    ring
  have hδ2 : (0 : ℚ) < (δ : ℚ) ^ 2 := by positivity
  have hpos : ∀ (c : ℕ → ℕ) (i : Fin N), 0 < δ * qmul N Q c i ↔ 0 < (P *ᵥ countsQ N c) i := by
    intro c i
    rw [← Int.cast_pos (R := ℚ), hsign, mul_pos_iff_of_pos_left hδ2]
  have hnonpos : ∀ (c : ℕ → ℕ) (i : Fin N),
      δ * qmul N Q c i ≤ 0 ↔ (P *ᵥ countsQ N c) i ≤ 0 := by
    intro c i
    rw [← not_lt, hpos, not_lt]
  unfold perceptron
  induction T with
  | zero =>
    have h0 : countsQ N (fun _ => 0) = 0 := by
      funext j
      simp [countsQ]
    exact ⟨fun h => absurd h (by simp), fun _ => ⟨by simp, by simp [loopN, h0]⟩⟩
  | succ T ih =>
    rw [loopN_succ]
    set s := loopN (fun _ => percStep N Q δ) T (false, fun _ => 0) with hs_def
    obtain ⟨ihT, ihF⟩ := ih
    unfold percStep
    by_cases hflag : s.1 = true
    · rw [ite_eq_left hflag]
      exact ⟨fun _ => ihT hflag, fun h => absurd h (by simp [hflag])⟩
    · rw [ite_eq_right hflag]
      have hF := ihF (by simpa using hflag)
      split_ifs with hall
      · refine ⟨fun _ i => (hpos s.2 i).mp (hall i i.2), fun h => absurd h (by simp)⟩
      · refine ⟨fun h => absurd h (by simp), fun _ => ?_⟩
        -- the incremented index has `(P c)_k ≤ 0`
        push Not at hall
        obtain ⟨i₀, hi₀, hle⟩ := hall
        have hlt : percIdx N Q δ s.2 < N := firstIdx_lt_iff.mpr ⟨i₀, hi₀, hle⟩
        set k : Fin N := ⟨percIdx N Q δ s.2, hlt⟩
        have hk : (P *ᵥ countsQ N s.2) k ≤ 0 := (hnonpos s.2 k).mp (firstIdx_spec hlt)
        have hc : countsQ N (fun l => if l = percIdx N Q δ s.2 then s.2 l + 1 else s.2 l) =
            countsQ N s.2 + Pi.single k 1 := by
          funext j
          simp only [countsQ, Pi.add_apply, Pi.single_apply]
          by_cases hj : j = k
          · subst hj
            simp [k]
          · have : (j : ℕ) ≠ percIdx N Q δ s.2 := fun h => hj (Fin.ext h)
            simp [this, hj]
        refine ⟨?_, ?_⟩
        · have hsumQ := congrArg (fun v : Fin N → ℚ => ∑ j, v j) hc
          simp only [countsQ, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single',
            Finset.mem_univ, ite_true] at hsumQ
          have h1 : ((∑ j : Fin N, (if (j : ℕ) = percIdx N Q δ s.2 then s.2 j + 1 else s.2 j) :
              ℕ) : ℚ) = ((T + 1 : ℕ) : ℚ) := by
            push_cast
            rw [← hF.1]
            push_cast
            convert hsumQ using 2
            split_ifs <;> simp
          exact_mod_cast h1
        · rw [hc]
          have := perceptron_step hs hd (countsQ N s.2) k hk
          push_cast
          linarith [hF.2]

/-! ### The cut -/

/-- **The cut lemma.** Let `P` be symmetric and idempotent, let the counts `c` sum to `T > 0` with
`c · P c ≤ T`, and let `j` be an index of the largest count. Every `x ∈ [0, 1]ᴺ` with `P x = x`
satisfies `x_j² T ≤ N³`. -/
theorem cut {P : Matrix (Fin N) (Fin N) ℚ} (hs : Pᵀ = P) (hi : P * P = P) {c : ℕ → ℕ} {T : ℕ}
    (hsum : ∑ j : Fin N, c j = T) (hq : countsQ N c ⬝ᵥ (P *ᵥ countsQ N c) ≤ T) {j : Fin N}
    (hj : ∀ l : Fin N, c l ≤ c j) {x : Fin N → ℚ} (hx : P *ᵥ x = x) (hx0 : ∀ l, 0 ≤ x l)
    (hx1 : ∀ l, x l ≤ 1) : x j ^ 2 * T ≤ (N : ℚ) ^ 3 := by
  set cq := countsQ N c
  have hcq0 : ∀ l, 0 ≤ cq l := fun l => by simp [cq, countsQ]
  -- `x_j c_j ≤ x · c`
  have h1 : x j * cq j ≤ x ⬝ᵥ cq := by
    rw [dotProduct]
    exact Finset.single_le_sum (f := fun l => x l * cq l)
      (fun l _ => mul_nonneg (hx0 l) (hcq0 l)) (Finset.mem_univ j)
  -- `x · c = x · P c`
  have h2 : x ⬝ᵥ cq = x ⬝ᵥ (P *ᵥ cq) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hs, hx]
  -- Cauchy–Schwarz: `(x · P c)² ≤ (x · x)(P c · P c)`
  have h3 : (x ⬝ᵥ (P *ᵥ cq)) ^ 2 ≤ (x ⬝ᵥ x) * ((P *ᵥ cq) ⬝ᵥ (P *ᵥ cq)) := by
    simp only [dotProduct]
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x (P *ᵥ cq)
    simpa [sq] using this
  have h4 : (P *ᵥ cq) ⬝ᵥ (P *ᵥ cq) = cq ⬝ᵥ (P *ᵥ cq) := by
    rw [dotProduct_mulVec (P *ᵥ cq), ← mulVec_transpose, hs, mulVec_mulVec, hi, dotProduct_comm]
  have h5 : x ⬝ᵥ x ≤ N := by
    calc x ⬝ᵥ x = ∑ l, x l * x l := rfl
      _ ≤ ∑ _l : Fin N, (1 : ℚ) := Finset.sum_le_sum fun l _ => by
          nlinarith [hx0 l, hx1 l]
      _ = N := by simp
  -- `N c_j ≥ T`
  have h6 : (T : ℚ) ≤ N * cq j := by
    have : T ≤ N * c j := by
      rw [← hsum]
      calc ∑ l : Fin N, c l ≤ ∑ _l : Fin N, c j := Finset.sum_le_sum fun l _ => hj l
        _ = N * c j := by simp
    simp only [cq, countsQ]
    exact_mod_cast this
  have hxj0 := hx0 j
  have hT0 : (0 : ℚ) ≤ T := by positivity
  have hN0 : (0 : ℚ) ≤ N := by positivity
  -- combine: `x_j² c_j² ≤ N T`, and `T ≤ N c_j`
  have h7 : (x j * cq j) ^ 2 ≤ N * T := by
    have hxc : 0 ≤ x j * cq j := mul_nonneg hxj0 (hcq0 j)
    calc (x j * cq j) ^ 2 ≤ (x ⬝ᵥ cq) ^ 2 := pow_le_pow_left₀ hxc h1 2
      _ = (x ⬝ᵥ (P *ᵥ cq)) ^ 2 := by rw [h2]
      _ ≤ (x ⬝ᵥ x) * ((P *ᵥ cq) ⬝ᵥ (P *ᵥ cq)) := h3
      _ ≤ N * T := by
          rw [h4]
          exact mul_le_mul h5 hq (by
            rw [← h4]; exact Finset.sum_nonneg fun l _ => mul_self_nonneg _) hN0
  have h8 : x j ^ 2 * T ^ 2 ≤ x j ^ 2 * (N * cq j) ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact pow_le_pow_left₀ hT0 h6 2
  have h9 : x j ^ 2 * T ^ 2 ≤ N ^ 2 * (N * T) := by
    calc x j ^ 2 * T ^ 2 ≤ x j ^ 2 * (N * cq j) ^ 2 := h8
      _ = N ^ 2 * (x j * cq j) ^ 2 := by ring
      _ ≤ N ^ 2 * (N * T) := mul_le_mul_of_nonneg_left h7 (by positivity)
  rcases eq_or_lt_of_le hT0 with hT | hT
  · rw [← hT]
    simp only [mul_zero]
    positivity
  · have : x j ^ 2 * T * T ≤ N ^ 3 * T := by nlinarith
    exact le_of_mul_le_mul_right this hT

/-- The cut after `T ≥ 4 N³` steps: `x_j ≤ 1 / 2`. -/
theorem cut_half {P : Matrix (Fin N) (Fin N) ℚ} (hs : Pᵀ = P) (hi : P * P = P) {c : ℕ → ℕ}
    {T : ℕ} (hT : 4 * N ^ 3 ≤ T) (hsum : ∑ j : Fin N, c j = T)
    (hq : countsQ N c ⬝ᵥ (P *ᵥ countsQ N c) ≤ T) {j : Fin N} (hj : ∀ l : Fin N, c l ≤ c j)
    {x : Fin N → ℚ} (hx : P *ᵥ x = x) (hx0 : ∀ l, 0 ≤ x l) (hx1 : ∀ l, x l ≤ 1) :
    2 * x j ≤ 1 := by
  have h := cut hs hi hsum hq hj hx hx0 hx1
  have hT' : (4 : ℚ) * N ^ 3 ≤ T := by exact_mod_cast hT
  have hN : (0 : ℚ) < N := by
    have : 0 < N := Fin.pos j
    exact_mod_cast this
  have hxj := hx0 j
  have h2 : x j ^ 2 * (4 * N ^ 3) ≤ N ^ 3 :=
    le_trans (mul_le_mul_of_nonneg_left hT' (sq_nonneg _)) h
  have h3 : x j ^ 2 * 4 ≤ 1 := by
    have hN3 : (0 : ℚ) < N ^ 3 := by positivity
    nlinarith
  nlinarith

end LinearProgramming
