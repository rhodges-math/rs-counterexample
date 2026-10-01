import Schubert.LinearProgramming.Polyhedra.Perturbation

/-!
# Small strictly positive solutions of homogeneous systems

If the integer system `M y = 0`, with `m` equations, `N` variables and entries at most `U`, has a
solution `y > 0`, then it has one with `1 ≤ y ≤ B`, where `B = basicBound (m + N) (N + N) U`
(`LinearProgramming.exists_bounded_of_strictlyFeasible`). Write the scaled condition `y ≥ 1` in
standard form, `M y = 0`, `y − s = 1`, `y, s ≥ 0`, and take a small basic solution
(`LinearProgramming.exists_small_basic_solution`).

This bounds the number of rescalings in a projection-and-rescaling algorithm. A coordinate that
has been halved `k` times caps it at `2⁻ᵏ` on the solutions in the unit cube, and the solution
`y / B` of the cube has every coordinate at least `1 / B`.

## Main results

* `LinearProgramming.exists_bounded_of_strictlyFeasible`: the rescaling-count bound.
* `LinearProgramming.exists_unitCube_of_strictlyFeasible`: the same, scaled into the unit cube.
-/

namespace LinearProgramming

open Matrix

/-- The matrix `[[M, 0], [I, −I]]` of the standard form `M y = 0`, `y − s = 1` of the condition
`y ≥ 1`. -/
def boxMatrix (m N : ℕ) (M : ℕ → ℕ → ℤ) : Matrix (Fin m ⊕ Fin N) (Fin N ⊕ Fin N) ℤ :=
  Matrix.of fun i j => match i, j with
    | Sum.inl i, Sum.inl j => M i j
    | Sum.inl _, Sum.inr _ => 0
    | Sum.inr i, Sum.inl j => if i = j then 1 else 0
    | Sum.inr i, Sum.inr j => if i = j then -1 else 0

theorem boxMatrix_mulVec {m N : ℕ} (M : ℕ → ℕ → ℤ) (v : Fin N ⊕ Fin N → ℚ) :
    toQ (boxMatrix m N M) *ᵥ v = Sum.elim
      (fun i : Fin m => ∑ j : Fin N, (M i j : ℚ) * v (Sum.inl j))
      (fun i : Fin N => v (Sum.inl i) - v (Sum.inr i)) := by
  funext i
  rcases i with i | i
  · simp [mulVec, dotProduct, boxMatrix, Fintype.sum_sum_type]
  · simp only [mulVec, dotProduct, toQ_apply, boxMatrix, of_apply, Fintype.sum_sum_type,
      Sum.elim_inr]
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [Ne.symm hk]) (by simp),
      Finset.sum_eq_single i (fun k _ hk => by simp [Ne.symm hk]) (by simp)]
    simp only [ite_true, Int.cast_one, one_mul, Int.cast_neg, neg_mul]
    ring

/-- **The rescaling-count bound.** If `M y = 0` has a solution `y > 0`, it has one with all
entries between `1` and `basicBound (m + N) (N + N) U`, where `U ≥ 1` bounds the entries of
`M`. -/
theorem exists_bounded_of_strictlyFeasible {m N : ℕ} {M : ℕ → ℕ → ℤ} {U : ℕ} (hU : 1 ≤ U)
    (hM : ∀ i < m, ∀ j < N, |M i j| ≤ U) (h : StrictlyFeasible m N M) :
    ∃ y : Fin N → ℚ, (∀ i : Fin m, ∑ j : Fin N, (M i j : ℚ) * y j = 0) ∧
      ∀ j, 1 ≤ y j ∧ y j ≤ basicBound (m + N) (N + N) U := by
  classical
  obtain ⟨y₀, hy₀, hpos⟩ := h
  -- a positive lower bound of `y₀`
  obtain ⟨μ, hμ, hμle⟩ : ∃ μ : ℚ, 0 < μ ∧ ∀ j, μ ≤ y₀ j := by
    rcases isEmpty_or_nonempty (Fin N) with hN | hN
    · exact ⟨1, one_pos, fun j => isEmptyElim j⟩
    · obtain ⟨j₀, _, hj₀⟩ := Finset.univ.exists_min_image y₀ Finset.univ_nonempty
      exact ⟨y₀ j₀, hpos j₀, fun j => hj₀ j (Finset.mem_univ _)⟩
  let y₁ : Fin N → ℚ := fun j => y₀ j / μ
  have hy₁ : ∀ j, 1 ≤ y₁ j := fun j => by
    rw [one_le_div hμ]
    exact hμle j
  let w : Fin N ⊕ Fin N → ℚ := Sum.elim y₁ (fun j => y₁ j - 1)
  have hw : ∀ j, 0 ≤ w j := by
    rintro (j | j)
    · exact le_trans zero_le_one (hy₁ j)
    · simp only [w, Sum.elim_inr]
      linarith [hy₁ j]
  let c : Fin m ⊕ Fin N → ℤ := Sum.elim (fun _ => 0) (fun _ => 1)
  have hMw : toQ (boxMatrix m N M) *ᵥ w = fun i => (c i : ℚ) := by
    rw [boxMatrix_mulVec]
    funext i
    rcases i with i | i
    · simp only [Sum.elim_inl, w, y₁, c, Int.cast_zero, mul_div_assoc']
      rw [← Finset.sum_div, hy₀ i, zero_div]
    · simp [w, c]
  have hbox : ∀ i j, |boxMatrix m N M i j| ≤ U := by
    have h1 : (1 : ℤ) ≤ U := by exact_mod_cast hU
    rintro (i | i) (j | j)
    · exact hM i i.2 j j.2
    · simp [boxMatrix]
    · simp only [boxMatrix, of_apply]
      split <;> simp [h1]
    · simp only [boxMatrix, of_apply]
      split <;> simp [h1]
  have hc : ∀ i, |c i| ≤ U := by
    rintro (i | i) <;> simp [c, hU]
  obtain ⟨w', hw', hMw', _, hle, _⟩ := exists_small_basic_solution (boxMatrix m N M) c hbox hc
    (f := fun _ => 0) (fun _ => le_rfl) hw hMw
  have hcard1 : Fintype.card (Fin m ⊕ Fin N) = m + N := by simp
  have hcard2 : Fintype.card (Fin N ⊕ Fin N) = N + N := by simp
  rw [hcard1, hcard2] at hle
  rw [boxMatrix_mulVec] at hMw'
  refine ⟨fun j => w' (Sum.inl j), fun i => ?_, fun j => ⟨?_, hle _⟩⟩
  · have := congrFun hMw' (Sum.inl i)
    simpa [c] using this
  · have := congrFun hMw' (Sum.inr j)
    simp only [Sum.elim_inr, c, Int.cast_one] at this
    linarith [hw' (Sum.inr j)]

/-- The rescaling-count bound in the unit cube: a solution `0 < x ≤ 1` of `M x = 0` with every
entry at least `1 / B`. -/
theorem exists_unitCube_of_strictlyFeasible {m N : ℕ} {M : ℕ → ℕ → ℤ} {U : ℕ} (hU : 1 ≤ U)
    (hM : ∀ i < m, ∀ j < N, |M i j| ≤ U) (h : StrictlyFeasible m N M) :
    ∃ x : Fin N → ℚ, (∀ i : Fin m, ∑ j : Fin N, (M i j : ℚ) * x j = 0) ∧
      ∀ j, 1 / (basicBound (m + N) (N + N) U : ℚ) ≤ x j ∧ x j ≤ 1 := by
  obtain ⟨y, hy, hb⟩ := exists_bounded_of_strictlyFeasible hU hM h
  have hB : (0 : ℚ) < basicBound (m + N) (N + N) U := by
    exact_mod_cast one_le_basicBound _ _ _
  refine ⟨fun j => y j / basicBound (m + N) (N + N) U, fun i => ?_, fun j => ⟨?_, ?_⟩⟩
  · simp only [mul_div_assoc']
    rw [← Finset.sum_div, hy i, zero_div]
  · exact div_le_div_of_nonneg_right (hb j).1 hB.le
  · rw [div_le_one hB]
    exact (hb j).2

end LinearProgramming
