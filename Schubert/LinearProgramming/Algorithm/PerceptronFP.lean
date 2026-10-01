import Schubert.LinearProgramming.Chubanov.Perceptron
import Schubert.LinearProgramming.Matrix.BareissFP

/-!
# The counting perceptron in polynomial time

The perceptron state `(flag, c)` is stored as the flag bit followed by the words of the counts
(`LinearProgramming.percEnc`). One step on strings (`LinearProgramming.percStrStep`) reads the
integer matrix `Q` and the scale `δ` as words. It computes the words of `δ (Q c)_i`, tests their
signs, and either sets the flag or increments one count. It is polynomial-time on all strings
(`LinearProgramming.percStrStep_mem_FP`), and so is the loop of `T` steps
(`LinearProgramming.percStrLoop_mem_FP`).

On encodings the string step computes the encoding of `LinearProgramming.percStep` whenever the
numbers `δ (Q c)_i` it tests fit their words (`LinearProgramming.percStrStep_percEnc`), and the
loop computes `LinearProgramming.perceptron` whenever this holds for all counts up to `T`
(`LinearProgramming.percStrLoop_eq`).

## Main definitions

* `LinearProgramming.percEnc W N s`: the encoding of a perceptron state.
* `LinearProgramming.percStrStep`, `LinearProgramming.percStrLoop`: the perceptron on strings.

## Main results

* `LinearProgramming.percStrLoop_mem_FP`: polynomial time.
* `LinearProgramming.percStrLoop_eq`: correctness on encodings.
-/

namespace LinearProgramming

open Complexity

/-! ### Tests on words -/

/-- The first digit of a string, `false` for the empty string. -/
def headBit (x : List Bool) : Bool := x[0]?.getD false

theorem headBit_cons (b : Bool) (x : List Bool) : headBit (b :: x) = b := rfl

/-- The comparison bit `0 < binValLE w`. -/
def nonzeroB (w : List Bool) : Bool := headBit (ltFlag (List.replicate w.length false) w)

theorem nonzeroB_iff (w : List Bool) : nonzeroB w = true ↔ 0 < binValLE w := by
  have h := ltFlag_eq_true_iff (List.replicate w.length false) w (by simp)
  rw [binValLE_replicate_false] at h
  rw [nonzeroB, ltFlag_eq _ _ (by simp)] at *
  rw [headBit, ← h]
  simp

/-- The positivity test of a word: sign bit clear and some digit set. -/
def wposB (w : List Bool) : Bool := !(msb w) && nonzeroB w

/-- **Positivity of a word** of an integer that fits. -/
theorem wposB_word {W : ℕ} {v : ℤ} (h : Fits W v) : wposB (word W v) = decide (0 < v) := by
  have hres : 0 < residue W v ↔ v ≠ 0 := by
    have hc := residue_cast W v
    have hfit := h
    rw [Fits, abs_lt] at hfit
    have hpow : (2 : ℤ) ^ (W - 1) ≤ 2 ^ W := pow_le_pow_right₀ (by norm_num) (by omega)
    constructor
    · intro hpos hv
      subst hv
      simp at hc
      omega
    · intro hv
      by_contra hz
      have h0 : (residue W v : ℤ) = 0 := by exact_mod_cast Nat.eq_zero_of_not_pos hz
      rw [hc] at h0
      obtain ⟨q, hq⟩ := Int.dvd_of_emod_eq_zero h0
      rcases lt_trichotomy q 0 with hq0 | hq0 | hq0
      · have : v ≤ -2 ^ W := by rw [hq]; nlinarith [pow_pos (show (0 : ℤ) < 2 by norm_num) W]
        linarith
      · exact hv (by rw [hq, hq0, mul_zero])
      · have : 2 ^ W ≤ v := by rw [hq]; nlinarith [pow_pos (show (0 : ℤ) < 2 by norm_num) W]
        linarith
  rw [wposB, msb_word h]
  by_cases hv : 0 < v
  · have hb : nonzeroB (word W v) = true := by
      rw [nonzeroB_iff, binValLE_word]
      exact hres.mpr hv.ne'
    simp [hv, hb, not_lt.mpr hv.le]
  · rcases lt_or_eq_of_le (not_lt.mp hv) with hneg | hzero
    · simp [hneg, hv]
    · subst hzero
      have hb : nonzeroB (word W 0) = false := by
        have := (nonzeroB_iff (word W 0)).not
        rw [binValLE_word] at this
        simpa [hres] using this
      simp [hb]

theorem headBit_mem_FP {X : List Bool → List Bool} (hX : X ∈ FP) :
    (fun z => [headBit (X z)]) ∈ FP :=
  getBit_mem_FP hX (UnaryFn.const 0)

theorem wposB_mem_FP {X : List Bool → List Bool} (hX : X ∈ FP) :
    FPPred fun z => wposB (X z) = true := by
  have h1 : FPPred fun z => msb (X z) = true := FPPred.of_flag (msb_mem_FP hX)
  have h2 : FPPred fun z => nonzeroB (X z) = true :=
    FPPred.of_flag (headBit_mem_FP (ltFlagFn_mem_FP
      ((UnaryFn.length hX).replicate_mem_FP false) hX))
  exact (h1.not.and h2).of_iff fun z => by simp [wposB]

/-! ### The perceptron step on strings -/

/-- The word of `(Q c)_i`, from the stored `N × N` matrix `Q` and the stored counts `c`. -/
def qmulStr (W N : ℕ) (Qx cx : List Bool) (i : ℕ) : List Bool :=
  sumWords W (fun j => wmul (blockOf W Qx (i * N + j)) (blockOf W cx j)) N

/-- The test `0 < δ (Q c)_i`. -/
def posStr (W N : ℕ) (Qx δx cx : List Bool) (i : ℕ) : Bool := wposB (wmul δx (qmulStr W N Qx cx i))

/-- The counts with entry `k` incremented. -/
def incrStr (W N k : ℕ) (cx : List Bool) : List Bool :=
  (List.range N).flatMap fun l =>
    if l = k then fitTo W (wadd (blockOf W cx l) (word W 1)) else blockOf W cx l

/-- **One perceptron step on strings**: keep a set flag; set it if every test passes; otherwise
increment the count of the first failing index. -/
def percStrStep (W N : ℕ) (Qx δx x : List Bool) : List Bool :=
  if headBit x = true then x
  else if ∀ i < N, posStr W N Qx δx (x.drop 1) i = true then true :: x.drop 1
  else false :: incrStr W N (firstIdx (fun k => posStr W N Qx δx (x.drop 1) k = false) N)
    (x.drop 1)

/-- The encoding of a perceptron state: the flag, then the words of the counts. -/
def percEnc (W N : ℕ) (s : Bool × (ℕ → ℕ)) : List Bool :=
  s.1 :: vecStr W (fun j => (s.2 j : ℤ)) N

/-- `T` perceptron steps on strings from zero counts. -/
def percStrLoop (W N T : ℕ) (Qx δx : List Bool) : List Bool :=
  loopN (fun _ => percStrStep W N Qx δx) T (percEnc W N (false, fun _ => 0))

theorem length_incrStr (W N k : ℕ) (cx : List Bool) : (incrStr W N k cx).length = N * W :=
  length_flatMap_range_const _ _ _ fun l => by
    split <;> simp

theorem length_percStrStep {W N : ℕ} (Qx δx : List Bool) {x : List Bool}
    (hx : x.length = 1 + N * W) : (percStrStep W N Qx δx x).length = 1 + N * W := by
  unfold percStrStep
  split_ifs
  · exact hx
  · simp [hx]
    omega
  · simp [length_incrStr]
    omega

theorem length_percEnc (W N : ℕ) (s : Bool × (ℕ → ℕ)) : (percEnc W N s).length = 1 + N * W := by
  simp [percEnc]
  omega

/-! ### Polynomial time -/

section Polytime

variable {W N : List Bool → ℕ} {Qx δx X : List Bool → List Bool}

theorem qmulStr_mem_FP {I : List Bool → ℕ} (hW : UnaryFn W) (hN : UnaryFn N) (hQ : Qx ∈ FP)
    (hX : X ∈ FP) (hI : UnaryFn I) : (fun z => qmulStr (W z) (N z) (Qx z) (X z) (I z)) ∈ FP := by
  have hW' := hW.comp pairFst_mem_FP
  refine sumWords_mem_FP (e := fun z j => wmul (blockOf (W z) (Qx z) (I z * N z + j))
    (blockOf (W z) (X z) j)) hW hN ?_ fun z j => by simp [length_wmul]
  exact wmul_mem_FP (blockOf_mem_FP hW' (mem_FP_comp pairFst_mem_FP hQ)
      (((hI.comp pairFst_mem_FP).mul (hN.comp pairFst_mem_FP)).add UnaryFn.idx))
    (blockOf_mem_FP hW' (mem_FP_comp pairFst_mem_FP hX) UnaryFn.idx)

theorem posStr_mem_FP {I : List Bool → ℕ} (hW : UnaryFn W) (hN : UnaryFn N) (hQ : Qx ∈ FP)
    (hδ : δx ∈ FP) (hX : X ∈ FP) (hI : UnaryFn I) :
    FPPred fun z => posStr (W z) (N z) (Qx z) (δx z) (X z) (I z) = true :=
  wposB_mem_FP (wmul_mem_FP hδ (qmulStr_mem_FP hW hN hQ hX hI))

theorem incrStr_mem_FP {K : List Bool → ℕ} (hW : UnaryFn W) (hN : UnaryFn N) (hK : UnaryFn K)
    (hX : X ∈ FP) : (fun z => incrStr (W z) (N z) (K z) (X z)) ∈ FP := by
  have hW' := hW.comp pairFst_mem_FP
  have hX' : (fun y => X (pairFst y)) ∈ FP := mem_FP_comp pairFst_mem_FP hX
  refine flatMap_range_mem_FP' hN (FPPred.ite_mem_FP (FPPred.eq UnaryFn.idx
    (hK.comp pairFst_mem_FP)) (fitTo_mem_FP hW' (wadd_mem_FP (blockOf_mem_FP hW' hX'
      UnaryFn.idx) (WordFn.const hW' 1))) (blockOf_mem_FP hW' hX' UnaryFn.idx))

theorem percStrStep_mem_FP (hW : UnaryFn W) (hN : UnaryFn N) (hQ : Qx ∈ FP) (hδ : δx ∈ FP)
    (hX : X ∈ FP) : (fun z => percStrStep (W z) (N z) (Qx z) (δx z) (X z)) ∈ FP := by
  have hT : (fun z => (X z).drop 1) ∈ FP := drop_mem_FP hX (UnaryFn.const 1)
  -- the tests, in the context `pair z (1^i)`
  have hpos := posStr_mem_FP (hW.comp pairFst_mem_FP) (hN.comp pairFst_mem_FP)
    (mem_FP_comp pairFst_mem_FP hQ) (mem_FP_comp pairFst_mem_FP hδ)
    (mem_FP_comp pairFst_mem_FP hT) UnaryFn.idx
  have hall : FPPred fun z => ∀ i < N z, posStr (W z) (N z) (Qx z) (δx z) ((X z).drop 1) i =
      true :=
    (FPPred.forall_lt hN hpos).of_iff fun z => by simp
  have hidx : UnaryFn fun z =>
      firstIdx (fun k => posStr (W z) (N z) (Qx z) (δx z) ((X z).drop 1) k = false) (N z) :=
    UnaryFn.firstIdx_of_iff hN hpos.not fun z j hj => by simp
  have hhead : FPPred fun z => headBit (X z) = true := FPPred.of_flag (headBit_mem_FP hX)
  exact FPPred.ite_mem_FP hhead hX (FPPred.ite_mem_FP hall
    (mem_FP_comp hT (Cobham.cons_mem_FP true))
    (mem_FP_comp (incrStr_mem_FP hW hN hidx hT) (Cobham.cons_mem_FP false)))

/-- **The perceptron loop is polynomial-time.** -/
theorem percStrLoop_mem_FP {T : List Bool → ℕ} (hW : UnaryFn W) (hN : UnaryFn N)
    (hT : UnaryFn T) (hQ : Qx ∈ FP) (hδ : δx ∈ FP) :
    (fun z => percStrLoop (W z) (N z) (T z) (Qx z) (δx z)) ∈ FP := by
  have hinit : (fun z => percEnc (W z) (N z) (false, fun _ => 0)) ∈ FP := by
    refine mem_FP_comp (vecStr_mem_FP (f := fun _ _ => 0) hN ?_) (Cobham.cons_mem_FP false)
    exact (WordFn.zero (hW.comp pairFst_mem_FP)).of_eq fun _ => by simp
  exact loopN_mem_FP (step := fun z _ x => percStrStep (W z) (N z) (Qx z) (δx z) x)
    (percStrStep_mem_FP (hW.comp ctx₂_mem_FP) (hN.comp ctx₂_mem_FP)
      (mem_FP_comp ctx₂_mem_FP hQ) (mem_FP_comp ctx₂_mem_FP hδ)
      (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP))
    hinit hT ((UnaryFn.const 1).add (hN.mul hW)) (fun z _ x hx => length_percStrStep _ _ hx)
    fun z => length_percEnc _ _ _

end Polytime

/-! ### What the loop computes -/

/-- Incrementing entry `k` of stored counts. -/
theorem incrStr_vecStr {W N k : ℕ} (c : ℕ → ℕ) :
    incrStr W N k (vecStr W (fun j => (c j : ℤ)) N) =
      vecStr W (fun j => ((if j = k then c j + 1 else c j : ℕ) : ℤ)) N := by
  unfold incrStr
  refine flatMap_range_eq_vecStr fun l hl => ?_
  rw [blockOf_vecStr hl]
  split_ifs with hlk
  · rw [wadd_word, fitTo_word]
    push_cast
    rfl
  · rfl


theorem qmulStr_vecStr {W N i : ℕ} {Q : ℕ → ℕ → ℤ} {c : ℕ → ℕ} (hi : i < N) :
    qmulStr W N (matStr W Q N N) (vecStr W (fun j => (c j : ℤ)) N) i = word W (qmul N Q c i) := by
  rw [qmulStr, sumWords_eq (f := fun j => Q i j * (c j : ℤ)) fun j hj => by
    rw [blockOf_matStr hi hj, blockOf_vecStr hj, wmul_word], qmul,
    ← Fin.sum_univ_eq_sum_range (fun j => Q i j * (c j : ℤ)) N]

/-- **One perceptron step on an encoding**, when the tested numbers fit. -/
theorem percStrStep_percEnc {W N : ℕ} {Q : ℕ → ℕ → ℤ} {δ : ℤ} (s : Bool × (ℕ → ℕ))
    (hfit : ∀ i < N, Fits W (δ * qmul N Q s.2 i)) :
    percStrStep W N (matStr W Q N N) (word W δ) (percEnc W N s) =
      percEnc W N (percStep N Q δ s) := by
  have hdrop : (percEnc W N s).drop 1 = vecStr W (fun j => (s.2 j : ℤ)) N := rfl
  have hpos : ∀ i < N, posStr W N (matStr W Q N N) (word W δ)
      (vecStr W (fun j => (s.2 j : ℤ)) N) i = decide (0 < δ * qmul N Q s.2 i) := fun i hi => by
    rw [posStr, qmulStr_vecStr hi, wmul_word, wposB_word (hfit i hi)]
  unfold percStrStep percStep
  rw [show headBit (percEnc W N s) = s.1 from rfl, hdrop]
  by_cases hflag : s.1 = true
  · rw [ite_eq_left hflag, ite_eq_left hflag]
  rw [ite_eq_right hflag, ite_eq_right hflag]
  have hall : (∀ i < N, posStr W N (matStr W Q N N) (word W δ)
      (vecStr W (fun j => (s.2 j : ℤ)) N) i = true) ↔ ∀ i < N, 0 < δ * qmul N Q s.2 i :=
    forall_congr' fun i => imp_congr_right fun hi => by rw [hpos i hi]; simp
  by_cases h : ∀ i < N, 0 < δ * qmul N Q s.2 i
  · rw [ite_eq_left (hall.mpr h), ite_eq_left h]
    rfl
  · rw [ite_eq_right (mt hall.mp h), ite_eq_right h]
    have hidx : firstIdx (fun k => posStr W N (matStr W Q N N) (word W δ)
        (vecStr W (fun j => (s.2 j : ℤ)) N) k = false) N = percIdx N Q δ s.2 := by
      unfold percIdx
      refine firstIdx_congr fun k hk => ?_
      rw [hpos k hk]
      simp
    rw [hidx, percEnc, incrStr_vecStr]

/-- **The perceptron loop on strings computes the perceptron**, when every tested number
`δ (Q c)_i` with counts at most `T` fits. -/
theorem percStrLoop_eq {W N T : ℕ} {Q : ℕ → ℕ → ℤ} {δ : ℤ}
    (hfit : ∀ c : ℕ → ℕ, (∀ j, c j ≤ T) → ∀ i < N, Fits W (δ * qmul N Q c i)) :
    percStrLoop W N T (matStr W Q N N) (word W δ) = percEnc W N (perceptron N Q δ T) := by
  unfold percStrLoop perceptron
  refine loopN_semiconj (percEnc W N) _ _ _ T fun r hr => percStrStep_percEnc _ fun i hi => ?_
  refine hfit _ (fun j => ?_) i hi
  -- the counts grow by at most one per step
  have : ∀ r : ℕ, ∀ j, (loopN (fun _ => percStep N Q δ) r (false, fun _ => 0)).2 j ≤ r := by
    intro r
    induction r with
    | zero => intro j; simp
    | succ r ih =>
      intro j
      rw [loopN_succ]
      unfold percStep
      split_ifs
      · exact (ih j).trans (Nat.le_succ r)
      · exact (ih j).trans (Nat.le_succ r)
      · simp only
        split_ifs
        · exact Nat.succ_le_succ (ih j)
        · exact (ih j).trans (Nat.le_succ r)
  exact (this r j).trans hr.le

end LinearProgramming
