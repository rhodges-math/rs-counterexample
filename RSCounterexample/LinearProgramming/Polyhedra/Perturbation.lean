import RSCounterexample.LinearProgramming.Polyhedra.GramCramer
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Field.Basic

/-!
# The perturbation lemma and the strict homogeneous form

A system `A x ≤ b` of `m` inequalities in `n` variables with integer data at most `U` is solvable
as soon as the slightly relaxed strict system `A x < b + ε` is, for `ε < 1 / B` with
`B = basicBound m (2n + m + 1) U` (`LinearProgramming.feasible_of_perturbed`). Indeed, write the
relaxed system in standard form `A x⁺ − A x⁻ + s − t 1 = b` with all variables nonnegative, and
minimize `t` over the small basic solutions (`LinearProgramming.exists_small_basic_solution`): the
minimum `t ≤ ε` is `0` or at least `1 / B`, so it is `0`.

Consequently, with `ε = 2⁻ᴱ` and `B < 2 ^ E`, solvability of `A x ≤ b` is equivalent to strict
solvability, `y > 0`, of the homogeneous system `M y = 0` with the integer matrix
`M = [2ᴱ A | −2ᴱ A | −(2ᴱ b + 1) | I_m]` (`LinearProgramming.feasible_iff_strictlyFeasible`).
This is the input of projection-and-rescaling algorithms (Chubanov, *A polynomial projection
algorithm for linear feasibility problems*, Math. Program. 153 (2015)).

Systems are given by their entries, indexed by natural numbers.

## Main definitions

* `LinearProgramming.Feasible m n A b`: `A x ≤ b` has a rational solution.
* `LinearProgramming.StrictlyFeasible m N M`: `M y = 0` has a rational solution with `y > 0`.
* `LinearProgramming.homEntry n A b E`: the entries of `[2ᴱ A | −2ᴱ A | −(2ᴱ b + 1) | I_m]`.

## Main results

* `LinearProgramming.feasible_of_perturbed`: the perturbation lemma.
* `LinearProgramming.feasible_iff_strictlyFeasible`: the strict homogeneous form.
-/

namespace LinearProgramming

open Matrix

/-- The system `A x ≤ b` of `m` inequalities in `n` variables has a rational solution. -/
def Feasible (m n : ℕ) (A : ℕ → ℕ → ℤ) (b : ℕ → ℤ) : Prop :=
  ∃ x : Fin n → ℚ, ∀ i : Fin m, ∑ j : Fin n, (A i j : ℚ) * x j ≤ b i

/-- The homogeneous system `M y = 0` of `m` equations in `N` variables has a rational solution
with all entries positive. -/
def StrictlyFeasible (m N : ℕ) (M : ℕ → ℕ → ℤ) : Prop :=
  ∃ y : Fin N → ℚ, (∀ i : Fin m, ∑ j : Fin N, (M i j : ℚ) * y j = 0) ∧ ∀ j, 0 < y j

/-! ### The perturbation lemma -/

/-- The columns `x⁺, x⁻, s, t` of the standard form `A x⁺ − A x⁻ + s − t 1 = b`. -/
abbrev StdCol (n m : ℕ) : Type := (Fin n ⊕ Fin n) ⊕ (Fin m ⊕ Unit)

/-- The matrix `[A | −A | I | −1]` of the standard form of `A x ≤ b`. -/
def stdMatrix (m n : ℕ) (A : ℕ → ℕ → ℤ) : Matrix (Fin m) (StdCol n m) ℤ :=
  Matrix.of fun i => Sum.elim (Sum.elim (fun j => A i j) (fun j => -A i j))
    (Sum.elim (fun k => if k = i then 1 else 0) (fun _ => -1))

theorem stdMatrix_mulVec {m n : ℕ} (A : ℕ → ℕ → ℤ) (v : StdCol n m → ℚ) (i : Fin m) :
    (toQ (stdMatrix m n A) *ᵥ v) i =
      ∑ j : Fin n, (A i j : ℚ) * (v (Sum.inl (Sum.inl j)) - v (Sum.inl (Sum.inr j))) +
        v (Sum.inr (Sum.inl i)) - v (Sum.inr (Sum.inr ())) := by
  simp only [mulVec, dotProduct, toQ_apply, stdMatrix, of_apply, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Fintype.univ_unit, Finset.sum_singleton]
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
  simp only [ite_true, Int.cast_one, one_mul, Int.cast_neg, neg_mul, mul_sub,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

theorem abs_stdMatrix_le {m n : ℕ} {A : ℕ → ℕ → ℤ} {U : ℕ} (hU : 1 ≤ U)
    (hA : ∀ i < m, ∀ j < n, |A i j| ≤ U) (i : Fin m) (j : StdCol n m) :
    |stdMatrix m n A i j| ≤ U := by
  rcases j with (j | j) | (k | u)
  · exact hA i i.2 j j.2
  · simpa [stdMatrix] using hA i i.2 j j.2
  · simp only [stdMatrix, of_apply, Sum.elim_inr, Sum.elim_inl]
    split <;> simp
    exact_mod_cast hU
  · simpa [stdMatrix] using hU

/-- **Perturbation lemma.** If the strict system `A x < b + ε` is solvable and `ε B < 1` with
`B = basicBound m (n + n + (m + 1)) U`, then `A x ≤ b` is solvable. -/
theorem feasible_of_perturbed {m n : ℕ} {A : ℕ → ℕ → ℤ} {b : ℕ → ℤ} {U : ℕ} (hU : 1 ≤ U)
    (hA : ∀ i < m, ∀ j < n, |A i j| ≤ U) (hb : ∀ i < m, |b i| ≤ U) {ε : ℚ}
    (hε : ε * basicBound m (n + n + (m + 1)) U < 1)
    (h : ∃ x : Fin n → ℚ, ∀ i : Fin m, ∑ j : Fin n, (A i j : ℚ) * x j < b i + ε) :
    Feasible m n A b := by
  classical
  obtain ⟨x₀, hx₀⟩ := h
  by_cases hε0 : ε ≤ 0
  · exact ⟨x₀, fun i => by linarith [hx₀ i]⟩
  push Not at hε0
  -- the objective `t`
  let f : StdCol n m → ℚ := Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (fun _ => 1))
  have hf : ∀ j, 0 ≤ f j := by
    rintro ((j | j) | (k | u)) <;> simp [f]
  have hfv : ∀ v : StdCol n m → ℚ, f ⬝ᵥ v = v (Sum.inr (Sum.inr ())) := fun v => by
    simp [f, dotProduct, Fintype.sum_sum_type]
  -- the solution of the relaxed system in standard form
  let w : StdCol n m → ℚ := Sum.elim (Sum.elim (fun j => max (x₀ j) 0) (fun j => max (-x₀ j) 0))
    (Sum.elim (fun i => b i + ε - ∑ j : Fin n, (A i j : ℚ) * x₀ j) (fun _ => ε))
  have hw : ∀ j, 0 ≤ w j := by
    rintro ((j | j) | (k | u))
    · exact le_max_right _ _
    · exact le_max_right _ _
    · simp only [w, Sum.elim_inr, Sum.elim_inl]
      linarith [hx₀ k]
    · exact hε0.le
  have hMw : toQ (stdMatrix m n A) *ᵥ w = fun i : Fin m => ((b i : ℤ) : ℚ) := by
    funext i
    rw [stdMatrix_mulVec]
    simp only [w, Sum.elim_inl, Sum.elim_inr]
    have : ∀ j, max (x₀ j) 0 - max (-x₀ j) 0 = x₀ j := fun j => by
      rcases le_total (x₀ j) 0 with h | h
      · rw [max_eq_right h, max_eq_left (by linarith)]
        ring
      · rw [max_eq_left h, max_eq_right (by linarith)]
        ring
    simp only [this]
    ring
  obtain ⟨w', hw', hMw', hfw', _, hsmall⟩ := exists_small_basic_solution (stdMatrix m n A)
    (fun i : Fin m => b i) (abs_stdMatrix_le hU hA) (fun i => hb i i.2) hf hw hMw
  have hcard : Fintype.card (StdCol n m) = n + n + (m + 1) := by simp
  rw [hcard, Fintype.card_fin] at hsmall
  rw [hfv, hfv] at hfw'
  simp only [w, Sum.elim_inr] at hfw'
  -- the minimum of `t` is zero
  have hB : (0 : ℚ) < basicBound m (n + n + (m + 1)) U := by
    exact_mod_cast one_le_basicBound _ _ _
  have ht : w' (Sum.inr (Sum.inr ())) = 0 := by
    by_contra hne
    have h1 := hsmall _ hne
    rw [div_le_iff₀ hB] at h1
    nlinarith [mul_le_mul_of_nonneg_right hfw' hB.le]
  refine ⟨fun j => w' (Sum.inl (Sum.inl j)) - w' (Sum.inl (Sum.inr j)), fun i => ?_⟩
  have := congrFun hMw' i
  rw [stdMatrix_mulVec, ht] at this
  linarith [hw' (Sum.inr (Sum.inl i))]

/-! ### The strict homogeneous form -/

/-- Entry `(i, j)` of the matrix `[2ᴱ A | −2ᴱ A | −(2ᴱ b + 1) | I_m]` with `n + n + 1 + m`
columns. -/
def homEntry (n : ℕ) (A : ℕ → ℕ → ℤ) (b : ℕ → ℤ) (E : ℕ) (i j : ℕ) : ℤ :=
  if j < n then 2 ^ E * A i j
  else if j < n + n then -(2 ^ E * A i (j - n))
  else if j = n + n then -(2 ^ E * b i + 1)
  else if j - (n + n + 1) = i then 1 else 0

/-- A sum over the columns of the homogeneous matrix, block by block. -/
theorem sum_fin_blocks {n m : ℕ} (g : ℕ → ℚ) :
    ∑ j : Fin (n + n + 1 + m), g j = ∑ j : Fin n, g j + ∑ j : Fin n, g (n + j) + g (n + n) +
      ∑ k : Fin m, g (n + n + 1 + k) := by
  rw [Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_add]
  simp [Fin.val_castAdd, Fin.val_natAdd]
  exact Finset.sum_congr rfl fun j _ => by rw [add_comm]

/-- The `i`-th equation of the homogeneous system, block by block. -/
theorem sum_homEntry {n m : ℕ} (A : ℕ → ℕ → ℤ) (b : ℕ → ℤ) (E : ℕ) {i : ℕ} (hi : i < m)
    (g : ℕ → ℚ) :
    ∑ j : Fin (n + n + 1 + m), (homEntry n A b E i j : ℚ) * g j =
      2 ^ E * ∑ j : Fin n, (A i j : ℚ) * (g j - g (n + j)) - (2 ^ E * b i + 1) * g (n + n) +
        g (n + n + 1 + i) := by
  rw [sum_fin_blocks (g := fun j => (homEntry n A b E i j : ℚ) * g j)]
  have h1 : ∀ j : Fin n, (homEntry n A b E i j : ℚ) * g j = 2 ^ E * A i j * g j := fun j => by
    simp [homEntry, j.2]
  have h2 : ∀ j : Fin n, (homEntry n A b E i (n + j) : ℚ) * g (n + j) =
      -(2 ^ E * A i j * g (n + j)) := fun j => by
    simp [homEntry, show ¬ (n + j : ℕ) < n by omega, show (n + j : ℕ) < n + n by omega]
  have h3 : (homEntry n A b E i (n + n) : ℚ) = -(2 ^ E * b i + 1) := by
    simp [homEntry]
  have h4 : ∑ k : Fin m, (homEntry n A b E i (n + n + 1 + k) : ℚ) * g (n + n + 1 + k) =
      g (n + n + 1 + i) := by
    rw [Finset.sum_eq_single ⟨i, hi⟩]
    · simp [homEntry, show ¬ (n + n + 1 + i < n) by omega, show ¬ (n + n + 1 + i < n + n) by omega,
        show n + n + 1 + i ≠ n + n by omega]
    · intro k _ hk
      have : (k : ℕ) ≠ i := fun h => hk (Fin.ext h)
      simp [homEntry, show ¬ (n + n + 1 + k : ℕ) < n by omega,
        show ¬ (n + n + 1 + k : ℕ) < n + n by omega, show (n + n + 1 + k : ℕ) ≠ n + n by omega,
        this]
    · simp
  simp only [h1, h2, h3, h4, Finset.sum_neg_distrib, mul_sub, Finset.mul_sum,
    Finset.sum_sub_distrib]
  ring_nf

/-- **The strict homogeneous form.** With data at most `U ≥ 1` and `basicBound m (2n + m + 1) U
< 2 ^ E`, the system `A x ≤ b` is solvable exactly when `M y = 0` has a solution `y > 0`, where
`M = [2ᴱ A | −2ᴱ A | −(2ᴱ b + 1) | I_m]`. -/
theorem feasible_iff_strictlyFeasible {m n : ℕ} {A : ℕ → ℕ → ℤ} {b : ℕ → ℤ} {U E : ℕ}
    (hU : 1 ≤ U) (hA : ∀ i < m, ∀ j < n, |A i j| ≤ U) (hb : ∀ i < m, |b i| ≤ U)
    (hE : basicBound m (n + n + (m + 1)) U < 2 ^ E) :
    Feasible m n A b ↔ StrictlyFeasible m (n + n + 1 + m) (homEntry n A b E) := by
  constructor
  · rintro ⟨x, hx⟩
    -- slack `s i = 2ᴱ (b i − (A x)ᵢ) + 1`
    let s : ℕ → ℚ := fun i => if hi : i < m then
      2 ^ E * (b i - ∑ j : Fin n, (A i j : ℚ) * x j) + 1 else 1
    let g : ℕ → ℚ := fun k =>
      if hk : k < n then max (x ⟨k, hk⟩) 0 + 1
      else if hk' : k < n + n then max (-x ⟨k - n, by omega⟩) 0 + 1
      else if k = n + n then 1
      else s (k - (n + n + 1))
    refine ⟨fun j => g j, fun i => ?_, fun j => ?_⟩
    · rw [sum_homEntry A b E i.2 g]
      have h1 : ∀ j : Fin n, g j - g (n + j) = x j := fun j => by
        simp only [g, dite_eq_left j.2, show ¬ (n + j : ℕ) < n by omega, dite_false,
          show (n + j : ℕ) < n + n by omega, dite_true]
        have : (⟨n + j - n, by omega⟩ : Fin n) = j := Fin.ext (by simp)
        rw [this]
        rcases le_total (x j) 0 with h | h
        · rw [max_eq_right h, max_eq_left (by linarith)]
          ring
        · rw [max_eq_left h, max_eq_right (by linarith)]
          ring
      have h2 : g (n + n) = 1 := by simp [g]
      have h3 : g (n + n + 1 + i) = 2 ^ E * (b i - ∑ j : Fin n, (A i j : ℚ) * x j) + 1 := by
        simp only [g, show ¬ (n + n + 1 + i : ℕ) < n by omega, dite_false,
          show ¬ (n + n + 1 + i : ℕ) < n + n by omega, show (n + n + 1 + i : ℕ) ≠ n + n by omega,
          ite_false, show n + n + 1 + (i : ℕ) - (n + n + 1) = i by omega, s, dite_eq_left i.2]
      simp only [h1, h2, h3]
      ring
    · simp only [g]
      split_ifs with h1 h2 h3
      · positivity
      · positivity
      · norm_num
      · simp only [s]
        split_ifs with h4
        · have := hx ⟨_, h4⟩
          have : (0 : ℚ) ≤ 2 ^ E * (b (j - (n + n + 1)) -
              ∑ k : Fin n, (A (j - (n + n + 1)) k : ℚ) * x k) := by
            apply mul_nonneg (by positivity)
            linarith
          linarith
        · norm_num
  · rintro ⟨y, hy, hpos⟩
    let g : ℕ → ℚ := fun k => if hk : k < n + n + 1 + m then y ⟨k, hk⟩ else 0
    have hg : ∀ j : Fin (n + n + 1 + m), y j = g j := fun j => by simp [g, j.2]
    have hlam : 0 < g (n + n) := by
      have := hpos ⟨n + n, by omega⟩
      simpa [g, show n + n < n + n + 1 + m by omega] using this
    apply feasible_of_perturbed (ε := 1 / 2 ^ E) hU hA hb
    · rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
      exact_mod_cast hE
    · refine ⟨fun j => (g j - g (n + j)) / g (n + n), fun i => ?_⟩
      have hyi := hy i
      simp only [hg] at hyi
      rw [sum_homEntry A b E i.2 g] at hyi
      have hs : 0 < g (n + n + 1 + i) := by
        have := hpos ⟨n + n + 1 + i, by omega⟩
        simpa [g, show n + n + 1 + (i : ℕ) < n + n + 1 + m by omega] using this
      have hsum : ∑ j : Fin n, (A i j : ℚ) * ((g j - g (n + j)) / g (n + n)) =
          (∑ j : Fin n, (A i j : ℚ) * (g j - g (n + j))) / g (n + n) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hsum, div_lt_iff₀ hlam]
      have h2E : (0 : ℚ) < 2 ^ E := by positivity
      have key : 2 ^ E * ((∑ j : Fin n, (A i j : ℚ) * (g j - g (n + j))) -
          (b i + 1 / 2 ^ E) * g (n + n)) = -g (n + n + 1 + i) := by
        field_simp
        linarith
      nlinarith

end LinearProgramming
