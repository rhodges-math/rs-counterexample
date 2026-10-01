import Schubert.LinearProgramming.Chubanov.Algorithm

/-!
# Deciding feasibility of `A x ≤ b`

Feasibility of `A x ≤ b` is strict feasibility of `M y = 0` for the homogeneous matrix
`M = [2ᴱ A | −2ᴱ A | −(2ᴱ b + 1) | I_m]` (`LinearProgramming.feasible_iff_strictlyFeasible`).
`M` has independent rows because of its identity block (`LinearProgramming.rowsIndep_homEntry`),
so the projection-and-rescaling algorithm decides it (`LinearProgramming.chubanov_iff`).
`LinearProgramming.decideFeasible` composes the two: it accepts exactly the feasible systems,
provided the parameters `E`, `K`, `R` and `T` are large enough for the data
(`LinearProgramming.decideFeasible_iff`).

## Main definitions

* `LinearProgramming.decideFeasible m n A b E R T`: the algorithm on the homogeneous matrix.

## Main results

* `LinearProgramming.rowsIndep_homEntry`: the homogeneous matrix has independent rows.
* `LinearProgramming.abs_homEntry_le`: its entries are at most `2ᴱ (U + 1)`.
* `LinearProgramming.decideFeasible_iff`: correctness.
-/

namespace LinearProgramming

open Matrix

/-- **The decision procedure**: the projection-and-rescaling algorithm with `R` rounds of `T`
perceptron steps on the homogeneous matrix of `A x ≤ b` with scale `2ᴱ`. -/
def decideFeasible (m n : ℕ) (A : ℕ → ℕ → ℤ) (b : ℕ → ℤ) (E R T : ℕ) : Bool :=
  chubanov m (n + n + 1 + m) (homEntry n A b E) R T

/-- The homogeneous matrix has independent rows: its last `m` columns form the identity. -/
theorem rowsIndep_homEntry (m n : ℕ) (A : ℕ → ℕ → ℤ) (b : ℕ → ℤ) (E : ℕ) :
    RowsIndep (homEntry n A b E) m (n + n + 1 + m) := by
  intro x hx
  funext i
  have h := hx ⟨n + n + 1 + i, by omega⟩
  rw [Finset.sum_eq_single i] at h
  · simpa [homEntry, show ¬ (n + n + 1 + (i : ℕ) < n) by omega,
      show ¬ (n + n + 1 + (i : ℕ) < n + n) by omega,
      show (n + n + 1 + (i : ℕ)) ≠ n + n by omega] using h
  · intro a _ ha
    have : (a : ℕ) ≠ i := fun h => ha (Fin.ext h)
    simp [homEntry, show ¬ (n + n + 1 + (i : ℕ) < n) by omega,
      show ¬ (n + n + 1 + (i : ℕ) < n + n) by omega,
      show (n + n + 1 + (i : ℕ)) ≠ n + n by omega, Ne.symm this]
  · simp

/-- The entries of the homogeneous matrix are at most `2ᴱ (U + 1)`. -/
theorem abs_homEntry_le {m n : ℕ} {A : ℕ → ℕ → ℤ} {b : ℕ → ℤ} {U : ℕ} (E : ℕ)
    (hA : ∀ i < m, ∀ j < n, |A i j| ≤ U) (hb : ∀ i < m, |b i| ≤ U) :
    ∀ i < m, ∀ j < n + n + 1 + m, |homEntry n A b E i j| ≤ 2 ^ E * (U + 1) := by
  intro i hi j hj
  have h2E : (1 : ℤ) ≤ 2 ^ E := one_le_pow₀ (by norm_num)
  have hU0 : (0 : ℤ) ≤ U := by positivity
  unfold homEntry
  split_ifs with h1 h2 h3 h4
  · rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 2 ^ E)]
    have := hA i hi j h1
    nlinarith
  · rw [abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 2 ^ E)]
    have := hA i hi (j - n) (by omega)
    nlinarith
  · rw [abs_neg]
    have := hb i hi
    calc |2 ^ E * b i + 1| ≤ |2 ^ E * b i| + |1| := abs_add_le _ _
      _ = 2 ^ E * |b i| + 1 := by
          rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 2 ^ E), abs_one]
      _ ≤ 2 ^ E * (U + 1) := by nlinarith
  · simp only [abs_one]
    nlinarith
  · simp only [abs_zero]
    positivity

/-- **The decision procedure is correct.** Let the data of the `m × n` system be at most
`U ≥ 1`, let `basicBound m (n + n + (m + 1)) U < 2ᴱ` (perturbation), let
`basicBound (m + N) (N + N) (2ᴱ (U + 1)) ≤ 2ᴷ` with `N = n + n + 1 + m` (rescaling count), and
let `R > N (K + 1)` and `T ≥ 4 N³ + 1`. Then the procedure accepts exactly the feasible systems. -/
theorem decideFeasible_iff {m n : ℕ} {A : ℕ → ℕ → ℤ} {b : ℕ → ℤ} {U E K R T : ℕ} (hU : 1 ≤ U)
    (hA : ∀ i < m, ∀ j < n, |A i j| ≤ U) (hb : ∀ i < m, |b i| ≤ U)
    (hE : basicBound m (n + n + (m + 1)) U < 2 ^ E)
    (hK : basicBound (m + (n + n + 1 + m)) ((n + n + 1 + m) + (n + n + 1 + m))
      (2 ^ E * (U + 1)) ≤ 2 ^ K)
    (hR : (n + n + 1 + m) * (K + 1) < R) (hT : 4 * (n + n + 1 + m) ^ 3 + 1 ≤ T) :
    decideFeasible m n A b E R T = true ↔ Feasible m n A b := by
  rw [feasible_iff_strictlyFeasible hU hA hb hE]
  have hUM : 1 ≤ 2 ^ E * (U + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  exact chubanov_iff (rowsIndep_homEntry m n A b E) hUM (fun i hi j hj => by
    have := abs_homEntry_le (A := A) (b := b) E hA hb i hi j hj
    exact_mod_cast this) hK hR hT

end LinearProgramming
