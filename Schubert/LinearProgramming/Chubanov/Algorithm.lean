import Schubert.LinearProgramming.Chubanov.Rescaling
import Schubert.LinearProgramming.Polyhedra.SmallSolution

/-!
# The projection-and-rescaling algorithm

A version of Chubanov's algorithm (S. Chubanov, *A polynomial projection algorithm for linear
feasibility problems*, Math. Program. 153 (2015)) that decides whether an integer system
`M y = 0` with independent rows has a solution `y > 0`. It uses exact integer arithmetic only.

The state is a flag and an exponent `k j` for every column. A round with the flag unset:

1. scales the columns, `M̃ = M diag(2^(R - k j))` (`LinearProgramming.scaled`);
2. computes `δ = det (M̃ M̃ᵀ)` and the integer projection `Q = δ P` onto `ker M̃` by fraction-free
   elimination (`LinearProgramming.bareiss_projBlock`);
3. runs `T` steps of the counting perceptron on `Q` (`LinearProgramming.perceptron`). On success,
   `P c > 0` is a positive kernel vector of `M̃`, so the flag is set. Otherwise the cut
   (`LinearProgramming.cut_half`) shows that every `x ∈ ker M̃ ∩ [0, 1]ᴺ` has `x_j ≤ 1/2` for the
   index `j` of the largest count, and `k j` grows by one.

The invariant (`LinearProgramming.ChubInv`) says that every `x ∈ ker M ∩ [0, 1]ᴺ` has
`2^(k j) x_j ≤ 1`. If `M y = 0, y > 0` is solvable, some such `x` has all entries at least
`1 / B`, where `B = basicBound (m + N) (N + N) U` (the rescaling-count bound,
`LinearProgramming.exists_unitCube_of_strictlyFeasible`). So `2^(k j) ≤ B` for every `j`. Hence
after `R > N (K + 1)` rounds, with `B ≤ 2^K`, the flag is set exactly when the system is solvable
(`LinearProgramming.chubanov_iff`).

## Main definitions

* `LinearProgramming.chubRound`: one round.
* `LinearProgramming.chubanov m N M R T`: the result after `R` rounds of `T` perceptron steps.

## Main results

* `LinearProgramming.chubInv_chubRound`: a round keeps the invariant.
* `LinearProgramming.chubanov_iff`: correctness.
-/

namespace LinearProgramming

open Matrix

/-- The Bareiss matrix and pivot of the projection in a round with exponents `k`. -/
def roundBareiss (m N : ℕ) (M : ℕ → ℕ → ℤ) (R : ℕ) (k : ℕ → ℕ) : (ℕ → ℕ → ℤ) × ℤ :=
  bareiss (projBlock (scaled M R k) m N) m

/-- The integer projection `δ P`: the trailing block of the Bareiss matrix. -/
def roundQ (m : ℕ) (B : (ℕ → ℕ → ℤ) × ℤ) (a b : ℕ) : ℤ := B.1 (m + a) (m + b)

/-- **One round** of the projection-and-rescaling algorithm. -/
def chubRound (m N : ℕ) (M : ℕ → ℕ → ℤ) (R T : ℕ) (s : Bool × (ℕ → ℕ)) : Bool × (ℕ → ℕ) :=
  if s.1 = true then s
  else if (perceptron N (roundQ m (roundBareiss m N M R s.2))
      (roundBareiss m N M R s.2).2 T).1 = true then (true, s.2)
  else (false, fun l => if l = argmaxIdx (fun j => ((perceptron N
      (roundQ m (roundBareiss m N M R s.2)) (roundBareiss m N M R s.2).2 T).2 j : ℤ)) N
    then s.2 l + 1 else s.2 l)

/-- **The projection-and-rescaling algorithm**: the flag after `R` rounds. -/
def chubanov (m N : ℕ) (M : ℕ → ℕ → ℤ) (R T : ℕ) : Bool :=
  (loopN (fun _ => chubRound m N M R T) R (false, fun _ => 0)).1

/-- The invariant after `r` rounds: a set flag certifies strict feasibility; otherwise the
exponents sum to `r`, and every `x ∈ ker M ∩ [0, 1]ᴺ` has `2^(k j) x_j ≤ 1`. -/
def ChubInv (m N : ℕ) (M : ℕ → ℕ → ℤ) (r : ℕ) (s : Bool × (ℕ → ℕ)) : Prop :=
  (s.1 = true → StrictlyFeasible m N M) ∧
    (s.1 = false → ∑ j : Fin N, s.2 j = r ∧
      ∀ x, KerBox m N M x → ∀ j : Fin N, 2 ^ s.2 j * x j ≤ 1)

variable {m N : ℕ} {M : ℕ → ℕ → ℤ}

theorem chubInv_zero : ChubInv m N M 0 (false, fun _ => 0) :=
  ⟨fun h => absurd h (by simp), fun _ => ⟨by simp, fun x hx j => by simpa using (hx.2 j).2⟩⟩

/-- **A round keeps the invariant**, for `M` with independent rows, `r < R` and
`T ≥ 4 N³ + 1`. -/
theorem chubInv_chubRound (hind : RowsIndep M m N) {R T r : ℕ} (hr : r < R)
    (hT : 4 * N ^ 3 + 1 ≤ T) {s : Bool × (ℕ → ℕ)} (hs : ChubInv m N M r s) :
    ChubInv m N M (r + 1) (chubRound m N M R T s) := by
  classical
  unfold chubRound
  by_cases hflag : s.1 = true
  · rw [ite_eq_left hflag]
    exact ⟨fun _ => hs.1 hflag, fun h => absurd hflag (by simp [h])⟩
  rw [ite_eq_right hflag]
  obtain ⟨hsum, hker⟩ := hs.2 (by simpa using hflag)
  have hk : ∀ j : Fin N, s.2 j ≤ R := fun j => by
    have : s.2 j ≤ ∑ l : Fin N, s.2 l :=
      Finset.single_le_sum (f := fun l : Fin N => s.2 l) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)
    omega
  set A := scaled M R s.2
  have hA : RowsIndep A m N := hind.scaled R s.2
  obtain ⟨hδpos, hδ, hQ⟩ := bareiss_projBlock hA
  set B := roundBareiss m N M R s.2
  have hQ' : ∀ a b : Fin N, (roundQ m B a b : ℚ) = (B.2 : ℚ) * projQ A m N a b := fun a b => by
    rw [show (B.2 : ℚ) = (gramQ A m N).det from hδ]
    exact hQ a b
  obtain ⟨hsucc, hfail⟩ := perceptron_spec (N := N) (Q := roundQ m B) (δ := B.2)
    (P := projQ A m N) hδpos.ne' hQ' proj_symm (proj_diag_le_one hA) T
  set p := perceptron N (roundQ m B) B.2 T
  split_ifs with hp
  · -- success: a positive kernel vector
    refine ⟨fun _ => ?_, fun h => absurd h (by simp)⟩
    set y := projQ A m N *ᵥ countsQ N p.2
    have hy := hsucc hp
    have hAy : rowsQ A m N *ᵥ y = 0 := mulVec_proj_mulVec hA _
    have hM := mulVec_scaled_down hAy
    refine ⟨fun j => 2 ^ (R - s.2 j) * y j, fun i => ?_, fun j => by
      have := hy j
      positivity⟩
    have := congrFun hM i
    rwa [rowsQ_mulVec_apply] at this
  · -- failure: rescale the column of the largest count
    have hp' : p.1 = false := by simpa using hp
    obtain ⟨hpsum, hpq⟩ := hfail hp'
    have hN : 0 < N := by
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · subst h0
        simp at hpsum
        omega
      · exact h0
    set jj := argmaxIdx (fun j => (p.2 j : ℤ)) N
    have hjj : jj < N := argmaxIdx_lt _ hN
    have hmax : ∀ l : Fin N, p.2 l ≤ p.2 (⟨jj, hjj⟩ : Fin N) := fun l => by
      have := le_argmaxIdx (fun j => (p.2 j : ℤ)) l.2
      exact_mod_cast this
    refine ⟨fun h => absurd h (by simp), fun _ => ⟨?_, fun x hx j => ?_⟩⟩
    · show ∑ l : Fin N, (if (l : ℕ) = jj then s.2 l + 1 else s.2 l) = r + 1
      have hsplit : ∀ l : Fin N, (if (l : ℕ) = jj then s.2 l + 1 else s.2 l) =
          s.2 l + (if (l : ℕ) = jj then 1 else 0) := fun l => by split_ifs <;> rfl
      rw [Finset.sum_congr rfl fun l _ => hsplit l, Finset.sum_add_distrib, hsum,
        Fin.sum_univ_eq_sum_range (fun i => if i = jj then 1 else 0) N,
        Finset.sum_ite_eq' (Finset.range N) jj (fun _ => 1),
        ite_eq_left (Finset.mem_range.mpr hjj)]
    · simp only
      by_cases hj : (j : ℕ) = jj
      · rw [ite_eq_left hj]
        -- the scaled kernel vector `x'`
        set x' : Fin N → ℚ := fun l => 2 ^ s.2 l * x l
        have hx'A : rowsQ A m N *ᵥ x' = 0 := mulVec_scaled_up hk hx.1
        have hx'0 : ∀ l, 0 ≤ x' l := fun l => mul_nonneg (by positivity) (hx.2 l).1
        have hx'1 : ∀ l, x' l ≤ 1 := fun l => hker x hx l
        have hcut := cut_half (P := projQ A m N) proj_symm (proj_idem hA) (by omega) hpsum hpq
          hmax (proj_mulVec_of_mulVec_eq_zero hx'A) hx'0 hx'1
        have hjeq : j = ⟨jj, hjj⟩ := Fin.ext hj
        subst hjeq
        simp only [x'] at hcut
        rw [pow_succ]
        linarith
      · rw [ite_eq_right hj]
        exact hker x hx j

theorem chubInv_loopN (hind : RowsIndep M m N) {R T : ℕ} (hT : 4 * N ^ 3 + 1 ≤ T) :
    ∀ r ≤ R, ChubInv m N M r (loopN (fun _ => chubRound m N M R T) r (false, fun _ => 0))
  | 0, _ => chubInv_zero
  | r + 1, hr => chubInv_chubRound hind (by omega) hT (chubInv_loopN hind hT r (by omega))

/-- **Correctness of the projection-and-rescaling algorithm.** Let `M` have independent rows and
entries at most `U ≥ 1`, let `basicBound (m + N) (N + N) U ≤ 2^K`, `R ≥ N (K + 1)` and
`T ≥ 4 N³ + 1`. Then the algorithm accepts exactly when `M y = 0` has a solution `y > 0`.
The strict inequality `R > N (K + 1)` also covers `N = 0`. -/
theorem chubanov_iff (hind : RowsIndep M m N) {U K R T : ℕ} (hU : 1 ≤ U)
    (hM : ∀ i < m, ∀ j < N, |M i j| ≤ U) (hK : basicBound (m + N) (N + N) U ≤ 2 ^ K)
    (hR : N * (K + 1) < R) (hT : 4 * N ^ 3 + 1 ≤ T) :
    chubanov m N M R T = true ↔ StrictlyFeasible m N M := by
  obtain ⟨hI1, hI2⟩ := chubInv_loopN hind hT R le_rfl
  refine ⟨hI1, fun hfeas => ?_⟩
  by_contra hne
  have hne' : chubanov m N M R T = false := by simpa using hne
  obtain ⟨hsum, hker⟩ := hI2 hne'
  obtain ⟨x, hx, hxb⟩ := exists_unitCube_of_strictlyFeasible hU hM hfeas
  have hB : (0 : ℚ) < basicBound (m + N) (N + N) U := by
    exact_mod_cast one_le_basicBound _ _ _
  have hkK : ∀ j : Fin N,
      (loopN (fun _ => chubRound m N M R T) R (false, fun _ => 0)).2 j ≤ K := by
    intro j
    have h1 := hker x ⟨funext fun i => hx i, fun l => ⟨le_trans (by positivity) (hxb l).1,
      (hxb l).2⟩⟩ j
    have h2 := (hxb j).1
    rw [div_le_iff₀ hB] at h2
    have h3 : (2 : ℚ) ^ (loopN (fun _ => chubRound m N M R T) R (false, fun _ => 0)).2 j ≤
        basicBound (m + N) (N + N) U := by
      nlinarith [pow_pos (show (0 : ℚ) < 2 by norm_num)
        ((loopN (fun _ => chubRound m N M R T) R (false, fun _ => 0)).2 j)]
    have h4 : (2 : ℕ) ^ (loopN (fun _ => chubRound m N M R T) R (false, fun _ => 0)).2 j ≤
        2 ^ K := le_trans (by exact_mod_cast h3) hK
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h4
  have : ∑ j : Fin N, (loopN (fun _ => chubRound m N M R T) R (false, fun _ => 0)).2 j ≤
      N * K := by
    calc _ ≤ ∑ _j : Fin N, K := Finset.sum_le_sum fun j _ => hkK j
      _ = N * K := by simp
  have hNK : N * K ≤ N * (K + 1) := Nat.mul_le_mul_left _ (by omega)
  omega

end LinearProgramming
