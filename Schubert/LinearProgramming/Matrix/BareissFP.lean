import Schubert.LinearProgramming.Matrix.Bareiss
import Schubert.LinearProgramming.Vectors.Matrix

/-!
# Fraction-free elimination in polynomial time

Fraction-free elimination on an `n × n` integer matrix stored as words of width `W`
(`LinearProgramming.matStr`). One step rewrites the matrix entry by entry from blocks of the old
matrix (`LinearProgramming.bareissStrStep`). It is polynomial-time whatever the string
(`LinearProgramming.bareissStrStep_mem_FP`), and so is the loop of `s` steps
(`LinearProgramming.bareissStrLoop_mem_FP`), since every step keeps the length `n² W`.

On the encoding of a matrix, a step computes the encoding of the next Bareiss matrix as soon as
the divisions it performs are exact and the numbers involved fit their words
(`LinearProgramming.bareissStrStep_matStr`). Along the whole run this holds when the leading
principal minors are nonzero and the words are long enough for the square of the largest bordered
minor (`LinearProgramming.bareissStrLoop_eq`): the numerators of step `k` are the previous pivot
times a bordered minor (`LinearProgramming.bareiss_int_num`).

## Main definitions

* `LinearProgramming.bareissStrStep W n k x`: step `k` on the matrix stored in `x`.
* `LinearProgramming.minorBound n U`: the bound `(n + 1)! (U + 1)^(n + 1)` on bordered minors.

## Main results

* `LinearProgramming.bareissStrLoop_mem_FP`: the loop is polynomial-time.
* `LinearProgramming.bareissStrLoop_eq`: the loop computes the Bareiss matrices.
-/

namespace LinearProgramming

open Complexity

/-- The divisor of step `k` on a stored matrix: the word of `1` at the first step, and otherwise
the diagonal block `(k - 1, k - 1)`. -/
def pivotStr (W n k : ℕ) (x : List Bool) : List Bool :=
  if k = 0 then word W 1 else blockOf W x ((k - 1) * n + (k - 1))

/-- The new entry at the row-major position `t` in step `k` of fraction-free elimination on the
`n × n` matrix stored in `x`. -/
def bareissEntryStr (W n k : ℕ) (x : List Bool) (t : ℕ) : List Bool :=
  if k < t / n ∧ k < t % n then
    fitTo W (wtdiv (wsub (wmul (blockOf W x (k * n + k)) (blockOf W x t))
        (wmul (blockOf W x (t / n * n + k)) (blockOf W x (k * n + t % n))))
      (pivotStr W n k x))
  else blockOf W x t

/-- Step `k` of fraction-free elimination on the `n × n` matrix stored in `x` in words of width
`W`. -/
def bareissStrStep (W n k : ℕ) (x : List Bool) : List Bool :=
  (List.range (n * n)).flatMap (bareissEntryStr W n k x)

theorem length_bareissEntryStr (W n k : ℕ) (x : List Bool) (t : ℕ) :
    (bareissEntryStr W n k x t).length = W := by
  unfold bareissEntryStr
  split <;> simp

theorem length_bareissStrStep (W n k : ℕ) (x : List Bool) :
    (bareissStrStep W n k x).length = n * n * W :=
  length_flatMap_range_const _ _ _ fun _ => length_bareissEntryStr _ _ _ _ _

theorem pivotStr_matStr {W n k : ℕ} {M : ℕ → ℕ → ℤ} (hk : k ≤ n) :
    pivotStr W n k (matStr W M n n) = word W (prevPivot M k) := by
  unfold pivotStr prevPivot
  split_ifs with hk0
  · rfl
  · rw [blockOf_matStr (by omega) (by omega)]

/-! ### Polynomial time -/

theorem pivotStr_mem_FP {W n K : List Bool → ℕ} {X : List Bool → List Bool}
    (hW : UnaryFn W) (hn : UnaryFn n) (hK : UnaryFn K) (hX : X ∈ FP) :
    (fun z => pivotStr (W z) (n z) (K z) (X z)) ∈ FP := by
  have hK1 : UnaryFn fun z => K z - 1 := hK.sub (UnaryFn.const 1)
  exact FPPred.ite_mem_FP (FPPred.eq hK (UnaryFn.const 0)) (WordFn.const hW 1)
    (blockOf_mem_FP hW hX ((hK1.mul hn).add hK1))

theorem bareissEntryStr_mem_FP {W n K T : List Bool → ℕ} {X : List Bool → List Bool}
    (hW : UnaryFn W) (hn : UnaryFn n) (hK : UnaryFn K) (hT : UnaryFn T) (hX : X ∈ FP) :
    (fun z => bareissEntryStr (W z) (n z) (K z) (X z) (T z)) ∈ FP := by
  have hb : ∀ {I : List Bool → ℕ}, UnaryFn I → (fun z => blockOf (W z) (X z) (I z)) ∈ FP :=
    fun hI => blockOf_mem_FP hW hX hI
  have hpiv := pivotStr_mem_FP hW hn hK hX
  exact FPPred.ite_mem_FP ((FPPred.lt hK (hT.div hn)).and (FPPred.lt hK (hT.mod hn)))
    (fitTo_mem_FP hW (wtdiv_mem_FP (wsub_mem_FP (wmul_mem_FP (hb ((hK.mul hn).add hK)) (hb hT))
      (wmul_mem_FP (hb (((hT.div hn).mul hn).add hK)) (hb ((hK.mul hn).add (hT.mod hn)))))
      hpiv))
    (hb hT)

theorem bareissStrStep_mem_FP {W n K : List Bool → ℕ} {X : List Bool → List Bool}
    (hW : UnaryFn W) (hn : UnaryFn n) (hK : UnaryFn K) (hX : X ∈ FP) :
    (fun z => bareissStrStep (W z) (n z) (K z) (X z)) ∈ FP :=
  flatMap_range_mem_FP' (hn.mul hn) (bareissEntryStr_mem_FP (hW.comp pairFst_mem_FP)
    (hn.comp pairFst_mem_FP) (hK.comp pairFst_mem_FP) UnaryFn.idx (mem_FP_comp pairFst_mem_FP hX))

/-- **The elimination loop is polynomial-time.** -/
theorem bareissStrLoop_mem_FP {W n s : List Bool → ℕ} {X : List Bool → List Bool}
    (hW : UnaryFn W) (hn : UnaryFn n) (hs : UnaryFn s) (hX : X ∈ FP)
    (hXlen : ∀ z, (X z).length = n z * n z * W z) :
    (fun z => loopN (bareissStrStep (W z) (n z)) (s z) (X z)) ∈ FP :=
  loopN_mem_FP (step := fun z k x => bareissStrStep (W z) (n z) k x)
    (bareissStrStep_mem_FP (hW.comp ctx₂_mem_FP) (hn.comp ctx₂_mem_FP) UnaryFn.idx
      (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP))
    hX hs ((hn.mul hn).mul hW) (fun _ _ _ _ => length_bareissStrStep _ _ _ _) hXlen

/-! ### What the loop computes -/

theorem blockOf_matStr' {W n t : ℕ} {M : ℕ → ℕ → ℤ} (ht : t < n * n) :
    blockOf W (matStr W M n n) t = word W (M (t / n) (t % n)) :=
  blockOf_vecStr ht

/-- **One step on the encoding of a matrix** computes the encoding of the next Bareiss matrix,
when the divisions of the step are exact and the numbers involved fit. -/
theorem bareissStrStep_matStr {W n k : ℕ} {M : ℕ → ℕ → ℤ}
    (hact : ∀ i < n, ∀ j < n, k < i → k < j →
      prevPivot M k ≠ 0 ∧ Fits W (prevPivot M k) ∧ Fits W (M k k * M i j - M i k * M k j) ∧
        prevPivot M k ∣ M k k * M i j - M i k * M k j) :
    bareissStrStep W n k (matStr W M n n) = matStr W (bareissStep k (prevPivot M k) M) n n := by
  refine flatMap_range_eq_vecStr fun t ht => ?_
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h] at ht
    · exact h
  have hi : t / n < n := (Nat.div_lt_iff_lt_mul hn).mpr ht
  have hj : t % n < n := Nat.mod_lt _ hn
  unfold bareissEntryStr bareissStep
  split_ifs with h
  · obtain ⟨hk1, hk2⟩ := h
    obtain ⟨hp0, hpf, hnf, hdvd⟩ := hact _ hi _ hj hk1 hk2
    have hkn : k < n := lt_trans hk1 hi
    have hpiv : pivotStr W n k (matStr W M n n) = word W (prevPivot M k) :=
      pivotStr_matStr hkn.le
    rw [blockOf_matStr hkn hkn, blockOf_matStr' ht, blockOf_matStr hi hkn,
      blockOf_matStr hkn hj, wmul_word, wmul_word, wsub_word, hpiv,
      wtdiv_word_of_dvd hnf hpf hp0 hdvd, fitTo_word]
  · exact blockOf_matStr' ht

/-- Fraction-free elimination as a loop on matrices. -/
theorem bareiss_fst_eq_loopN {R : Type*} [CommRing R] [Div R] (H : ℕ → ℕ → R) (s : ℕ) :
    (bareiss H s).1 = loopN (fun k M => bareissStep k (prevPivot M k) M) s H := by
  induction s with
  | zero => rfl
  | succ s ih => rw [bareiss_fst_succ, ih, loopN_succ]

/-- The bound `(n + 1)! (U + 1)^(n + 1)` on the bordered minors of order at most `n + 1` of a
matrix with entries at most `U`. -/
def minorBound (n U : ℕ) : ℕ := (n + 1).factorial * (U + 1) ^ (n + 1)

theorem one_le_minorBound (n U : ℕ) : 1 ≤ minorBound n U :=
  Nat.mul_le_mul (Nat.factorial_pos _) (Nat.one_le_pow _ _ (by omega))

/-- Bordered minors of order at most `n + 1` inside an `n × n` matrix with entries at most `U`
are at most `minorBound n U`. -/
theorem abs_borderedMinor_le_minorBound {H : ℕ → ℕ → ℤ} {U n k i j : ℕ} (hk : k ≤ n)
    (hi : i < n) (hj : j < n) (hH : ∀ a < n, ∀ b < n, |H a b| ≤ U) :
    |borderedMinor H k i j| ≤ minorBound n U := by
  have h := abs_borderedMinor_le (U := (U : ℤ)) hk hi hj hH
  have h2 : ((k + 1).factorial : ℤ) * (U : ℤ) ^ (k + 1) ≤ minorBound n U := by
    unfold minorBound
    push_cast
    apply mul_le_mul (by exact_mod_cast Nat.factorial_le (by omega))
    · calc (U : ℤ) ^ (k + 1) ≤ ((U : ℤ) + 1) ^ (k + 1) :=
            pow_le_pow_left₀ (by positivity) (by linarith) _
        _ ≤ ((U : ℤ) + 1) ^ (n + 1) := pow_le_pow_right₀ (by linarith) (by omega)
    · positivity
    · positivity
  linarith

/-- The pivots of the first `n` steps are at most `minorBound n U`. -/
theorem abs_leadMinor_le_minorBound {H : ℕ → ℕ → ℤ} {U n k : ℕ} (hk : k ≤ n)
    (hH : ∀ a < n, ∀ b < n, |H a b| ≤ U) : |leadMinor H k| ≤ minorBound n U := by
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · subst h0
    rw [leadMinor_zero, abs_one]
    exact_mod_cast one_le_minorBound n U
  · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [← borderedMinor_self]
    exact abs_borderedMinor_le_minorBound (by omega) (by omega) (by omega) hH

/-- **The elimination loop computes the Bareiss matrices** of an `n × n` matrix with entries at
most `U`, for `s ≤ n` steps, if the leading principal minors of orders `1, …, s - 1` are nonzero
and the square of `minorBound n U` fits the words. -/
theorem bareissStrLoop_eq {W n s U : ℕ} {H : ℕ → ℕ → ℤ} (hs : s ≤ n)
    (hH : ∀ a < n, ∀ b < n, |H a b| ≤ U) (hlead : ∀ l, 1 ≤ l → l < s → leadMinor H l ≠ 0)
    (hW : (minorBound n U : ℤ) ^ 2 < 2 ^ (W - 1)) :
    loopN (bareissStrStep W n) s (matStr W H n n) = matStr W (bareiss H s).1 n n := by
  rw [bareiss_fst_eq_loopN]
  refine loopN_semiconj (fun M => matStr W M n n) _ _ H s fun k hk => ?_
  rw [← bareiss_fst_eq_loopN]
  refine bareissStrStep_matStr fun i hi j hj hki hkj => ?_
  have h2 := (bareiss_int_eq_borderedMinor H k fun l h1 h2 => hlead l h1 (by omega)).2
  have hpiv : prevPivot (bareiss H k).1 k = leadMinor H k := by
    rw [← bareiss_snd]
    exact h2
  have hnum := bareiss_int_num H k (fun l h1 h2 => hlead l h1 (by omega)) hki hkj
  rw [h2] at hnum
  rw [hpiv]
  have hB1 : (1 : ℤ) ≤ minorBound n U := by exact_mod_cast one_le_minorBound n U
  have hp := abs_leadMinor_le_minorBound (k := k) (by omega) hH
  have hm := abs_borderedMinor_le_minorBound (k := k + 1) (i := i) (j := j) (by omega) hi hj hH
  refine ⟨?_, ?_, ?_, ⟨_, hnum⟩⟩
  · rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      simp [leadMinor_zero]
    · exact hlead k hpos hk
  · unfold Fits
    calc |leadMinor H k| ≤ minorBound n U := hp
      _ ≤ (minorBound n U : ℤ) ^ 2 := by nlinarith
      _ < 2 ^ (W - 1) := hW
  · unfold Fits
    rw [hnum, abs_mul]
    calc |leadMinor H k| * |borderedMinor H (k + 1) i j| ≤ minorBound n U * minorBound n U :=
          mul_le_mul hp hm (abs_nonneg _) (by linarith)
      _ = (minorBound n U : ℤ) ^ 2 := by ring
      _ < 2 ^ (W - 1) := hW

end LinearProgramming
