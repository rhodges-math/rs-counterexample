import RSCounterexample.LinearProgramming.Algorithm.RoundFP
import RSCounterexample.LinearProgramming.Chubanov.Decide

/-!
# The parameters of the algorithm

All parameters of the decision procedure are explicit polynomials in the number `m` of
inequalities, the number `n` of variables and the input length `L`, whose entries are at most
`2 ^ L` in absolute value:

* `LinearProgramming.pE`: the perturbation exponent, `basicBound m (2n + m + 1) 2^L < 2^E`;
* `LinearProgramming.pK`: the bound `2^K` on the rescaling count;
* `LinearProgramming.pR`, `LinearProgramming.pT`: the numbers of rounds and of perceptron steps;
* `LinearProgramming.pW`: the word width, enough for every number the algorithm handles.

The bounds come from `k! ≤ 2^(k k)` (`LinearProgramming.factorial_le_two_pow`), so every bound
of the form `k! x^k` is a power of two with a polynomial exponent
(`LinearProgramming.basicBound_le_two_pow`, `LinearProgramming.minorBound_le_two_pow`).

## Main results

* `LinearProgramming.pE_spec`, `LinearProgramming.pK_spec`: the hypotheses of
  `LinearProgramming.decideFeasible_iff`.
* `LinearProgramming.abs_projBlock_le`: the entries of the projection matrices of all rounds.
* `LinearProgramming.pW_spec`: the words are long enough for the elimination and the perceptron.
-/

namespace LinearProgramming

/-! ### Powers of two -/

theorem factorial_le_two_pow (k : ℕ) : k.factorial ≤ 2 ^ (k * k) := by
  rw [pow_mul]
  exact (Nat.factorial_le_pow k).trans (Nat.pow_le_pow_left Nat.lt_two_pow_self.le k)

theorem succ_le_two_pow (k : ℕ) : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self

theorem basicBound_le_two_pow {r k U a b : ℕ} (hr : r + 1 ≤ 2 ^ a) (hU : U + 1 ≤ 2 ^ b) :
    basicBound r k U ≤ 2 ^ (k * k + k * (a + 2 * b)) := by
  have h1 : (r + 1) * (U + 1) ^ 2 ≤ 2 ^ (a + 2 * b) := by
    calc (r + 1) * (U + 1) ^ 2 ≤ 2 ^ a * (2 ^ b) ^ 2 :=
          Nat.mul_le_mul hr (Nat.pow_le_pow_left hU 2)
      _ = 2 ^ (a + 2 * b) := by rw [← pow_mul, ← pow_add]; ring_nf
  calc basicBound r k U = k.factorial * ((r + 1) * (U + 1) ^ 2) ^ k := rfl
    _ ≤ 2 ^ (k * k) * (2 ^ (a + 2 * b)) ^ k :=
        Nat.mul_le_mul (factorial_le_two_pow k) (Nat.pow_le_pow_left h1 k)
    _ = 2 ^ (k * k + k * (a + 2 * b)) := by rw [← pow_mul, ← pow_add]; ring_nf

theorem minorBound_le_two_pow {n U b : ℕ} (hU : U + 1 ≤ 2 ^ b) :
    minorBound n U ≤ 2 ^ ((n + 1) * (n + 1) + (n + 1) * b) := by
  calc minorBound n U = (n + 1).factorial * (U + 1) ^ (n + 1) := rfl
    _ ≤ 2 ^ ((n + 1) * (n + 1)) * (2 ^ b) ^ (n + 1) :=
        Nat.mul_le_mul (factorial_le_two_pow _) (Nat.pow_le_pow_left hU _)
    _ = 2 ^ ((n + 1) * (n + 1) + (n + 1) * b) := by rw [← pow_mul, ← pow_add]; ring_nf

/-! ### The parameters -/

/-- The number `N = 2n + 1 + m` of columns of the homogeneous matrix. -/
def pN (m n : ℕ) : ℕ := n + n + 1 + m

/-- The perturbation exponent `E`. -/
def pE (m n L : ℕ) : ℕ :=
  (n + n + (m + 1)) * (n + n + (m + 1)) + (n + n + (m + 1)) * (m + 2 * (L + 1)) + 1

/-- The exponent `K` with `basicBound (m + N) (N + N) (2^E (2^L + 1)) ≤ 2^K`. -/
def pK (m n L : ℕ) : ℕ :=
  (pN m n + pN m n) * (pN m n + pN m n) +
    (pN m n + pN m n) * ((m + pN m n) + 2 * (pE m n L + L + 2))

/-- The number of rounds `R = N (K + 1) + 1`. -/
def pR (m n L : ℕ) : ℕ := pN m n * (pK m n L + 1) + 1

/-- The number of perceptron steps `T = 4 N³ + 1`. -/
def pT (m n : ℕ) : ℕ := 4 * pN m n ^ 3 + 1

/-- The exponent `E + L + 1 + R` of the scaled entries. -/
def pA (m n L : ℕ) : ℕ := pE m n L + L + 1 + pR m n L

/-- The exponent `2 (E + L + 1 + R) + N` of the entries of the projection matrices. -/
def pH (m n L : ℕ) : ℕ := 2 * pA m n L + pN m n

/-- The exponent bounding `minorBound (m + N) 2^H`. -/
def pMB (m n L : ℕ) : ℕ :=
  (m + pN m n + 1) * (m + pN m n + 1) + (m + pN m n + 1) * (pH m n L + 1)

/-- The word width. -/
def pW (m n L : ℕ) : ℕ := 2 * pMB m n L + pN m n * pT m n + pT m n + pR m n L + L + 2

/-! ### The hypotheses of the decision procedure -/

theorem two_pow_add_one_le (L : ℕ) : 2 ^ L + 1 ≤ 2 ^ (L + 1) := by
  rw [pow_succ]
  have := Nat.one_le_two_pow (n := L)
  omega

/-- The perturbation bound. -/
theorem pE_spec (m n L : ℕ) : basicBound m (n + n + (m + 1)) (2 ^ L) < 2 ^ pE m n L := by
  refine lt_of_le_of_lt (basicBound_le_two_pow (succ_le_two_pow m) (two_pow_add_one_le L)) ?_
  exact Nat.pow_lt_pow_right (by norm_num) (by unfold pE; omega)

/-- The rescaling-count bound. -/
theorem pK_spec (m n L : ℕ) :
    basicBound (m + pN m n) (pN m n + pN m n) (2 ^ pE m n L * (2 ^ L + 1)) ≤ 2 ^ pK m n L := by
  have hb : 2 ^ pE m n L * (2 ^ L + 1) + 1 ≤ 2 ^ (pE m n L + L + 2) := by
    have h1 : 2 ^ pE m n L * (2 ^ L + 1) ≤ 2 ^ (pE m n L + L + 1) := by
      rw [show pE m n L + L + 1 = pE m n L + (L + 1) by ring, pow_add]
      exact Nat.mul_le_mul_left _ (two_pow_add_one_le L)
    have h2 : 2 ^ (pE m n L + L + 2) = 2 ^ (pE m n L + L + 1) + 2 ^ (pE m n L + L + 1) := by
      rw [show pE m n L + L + 2 = pE m n L + L + 1 + 1 by ring, pow_succ]
      ring
    have h3 := Nat.one_le_two_pow (n := pE m n L + L + 1)
    omega
  exact (basicBound_le_two_pow (succ_le_two_pow (m + pN m n)) hb).trans le_rfl

theorem pR_spec (m n L : ℕ) : pN m n * (pK m n L + 1) < pR m n L := by
  unfold pR
  omega

/-! ### The sizes of the numbers -/

/-- **The entries of the projection matrices of all rounds** are at most `2^H`, for a matrix
`M` with entries at most `2^E (2^L + 1)` and any exponents. -/
theorem abs_projBlock_le {m n L : ℕ} {M : ℕ → ℕ → ℤ}
    (hM : ∀ i < m, ∀ j < pN m n, |M i j| ≤ 2 ^ pE m n L * (2 ^ L + 1)) (k : ℕ → ℕ) :
    ∀ a < m + pN m n, ∀ b < m + pN m n,
      |projBlock (scaled M (pR m n L) k) m (pN m n) a b| ≤ ((2 ^ pH m n L : ℕ) : ℤ) := by
  set N := pN m n
  set R := pR m n L
  have hA : ∀ i < m, ∀ j < N, |scaled M R k i j| ≤ 2 ^ pA m n L := by
    intro i hi j hj
    unfold scaled
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 2 ^ (R - k j))]
    have h1 := hM i hi j hj
    have h2 : (2 : ℤ) ^ pE m n L * (2 ^ L + 1) ≤ 2 ^ (pE m n L + L + 1) := by
      rw [show pE m n L + L + 1 = pE m n L + (L + 1) by ring, pow_add]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact_mod_cast two_pow_add_one_le L
    have h3 : (2 : ℤ) ^ (R - k j) ≤ 2 ^ R := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    calc |M i j| * 2 ^ (R - k j) ≤ 2 ^ (pE m n L + L + 1) * 2 ^ R :=
          mul_le_mul (h1.trans h2) h3 (by positivity) (by positivity)
      _ = 2 ^ pA m n L := by rw [← pow_add]; rfl
  have hApos : (1 : ℤ) ≤ 2 ^ pA m n L := one_le_pow₀ (by norm_num)
  have hAH : (2 : ℤ) ^ pA m n L ≤ 2 ^ pH m n L :=
    pow_le_pow_right₀ (by norm_num) (by unfold pH; omega)
  intro a ha b hb
  push_cast
  unfold projBlock
  split_ifs with h1 h2 h3 h4
  · -- a Gram entry
    unfold gram
    calc |∑ j : Fin N, scaled M R k a j * scaled M R k b j|
        ≤ ∑ j : Fin N, |scaled M R k a j * scaled M R k b j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin N, (2 : ℤ) ^ pA m n L * 2 ^ pA m n L := Finset.sum_le_sum fun j _ => by
          rw [abs_mul]
          exact mul_le_mul (hA a h1 j j.2) (hA b h2 j j.2) (abs_nonneg _) (by positivity)
      _ = N * (2 ^ pA m n L * 2 ^ pA m n L) := by simp
      _ ≤ 2 ^ N * (2 ^ pA m n L * 2 ^ pA m n L) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast Nat.lt_two_pow_self.le
      _ = 2 ^ pH m n L := by
          rw [← pow_add, ← pow_add]
          show (2 : ℤ) ^ (N + (pA m n L + pA m n L)) = 2 ^ (2 * pA m n L + N)
          congr 1
          omega
  · exact (hA a h1 _ (by omega)).trans hAH
  · exact (hA b h3 _ (by omega)).trans hAH
  · simp only [abs_one]
    exact one_le_pow₀ (by norm_num)
  · simp only [abs_zero]
    positivity

/-- **The words are long enough** for the elimination and the perceptron, for the counts and
the exponents, and for the input entries. -/
theorem pW_spec (m n L : ℕ) :
    ((pN m n * pT m n + 1 : ℕ) : ℤ) * (minorBound (m + pN m n) (2 ^ pH m n L) : ℤ) ^ 2 <
        2 ^ (pW m n L - 1) ∧
      (pT m n : ℤ) < 2 ^ (pW m n L - 1) ∧ pR m n L < 2 ^ pW m n L ∧ L ≤ pW m n L := by
  have hMB : minorBound (m + pN m n) (2 ^ pH m n L) ≤ 2 ^ pMB m n L := by
    have := minorBound_le_two_pow (n := m + pN m n) (two_pow_add_one_le (pH m n L))
    simpa [pMB] using this
  have hNT : pN m n * pT m n + 1 ≤ 2 ^ (pN m n * pT m n) := succ_le_two_pow _
  have hW1 : pW m n L - 1 = 2 * pMB m n L + pN m n * pT m n + pT m n + pR m n L + L + 1 := by
    unfold pW
    omega
  refine ⟨?_, ?_, ?_, by unfold pW; omega⟩
  · have h1 : (pN m n * pT m n + 1) * minorBound (m + pN m n) (2 ^ pH m n L) ^ 2 <
        2 ^ (pW m n L - 1) := by
      calc (pN m n * pT m n + 1) * minorBound (m + pN m n) (2 ^ pH m n L) ^ 2
          ≤ 2 ^ (pN m n * pT m n) * (2 ^ pMB m n L) ^ 2 :=
            Nat.mul_le_mul hNT (Nat.pow_le_pow_left hMB 2)
        _ = 2 ^ (pN m n * pT m n + 2 * pMB m n L) := by rw [← pow_mul, ← pow_add]; ring_nf
        _ < 2 ^ (pW m n L - 1) := Nat.pow_lt_pow_right (by norm_num) (by rw [hW1]; omega)
    exact_mod_cast h1
  · have h1 : pT m n < 2 ^ (pW m n L - 1) :=
      lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by rw [hW1]; omega))
    exact_mod_cast h1
  · have hle : pR m n L ≤ pW m n L := by
      unfold pW
      omega
    exact lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) hle)

end LinearProgramming
