import Schubert.LinearProgramming.Algorithm.PerceptronFP
import Schubert.LinearProgramming.Chubanov.Algorithm

/-!
# A round of the projection-and-rescaling algorithm in polynomial time

The state `(flag, k)` of the algorithm is stored like a perceptron state
(`LinearProgramming.percEnc`), and the homogeneous `m × N` matrix `M` as words
(`LinearProgramming.matStr`). One round on strings (`LinearProgramming.roundStrStep`):

1. reads the exponents `k j`, as numbers capped at `R`;
2. writes the matrix `[[M̃ M̃ᵀ, M̃], [M̃ᵀ, I]]` for the scaled matrix `M̃ = M diag(2^(R - k j))`
   (`LinearProgramming.projStr`);
3. runs `m` steps of fraction-free elimination on it and reads off the integer projection `Q` and
   the pivot `δ` (`LinearProgramming.qStr`, `LinearProgramming.deltaStr`);
4. runs the perceptron for `T` steps, and either sets the flag or increments the exponent of the
   largest count (`LinearProgramming.argmaxStr`).

The round is polynomial-time on all strings (`LinearProgramming.roundStrStep_mem_FP`). On
encodings it computes `LinearProgramming.chubRound` when the exponents are at most `R` and the
numbers fit their words (`LinearProgramming.roundStrStep_percEnc`).

## Main definitions

* `LinearProgramming.roundStrStep W m N R T Mx x`: one round on strings.

## Main results

* `LinearProgramming.roundStrStep_mem_FP`: polynomial time.
* `LinearProgramming.roundStrStep_percEnc`: correctness on encodings.
-/

namespace LinearProgramming

open Complexity

noncomputable section

/-! ### The round on strings -/

/-- The exponent `k j`, read from the stored exponents as a number capped at `R`. -/
def kOf (W R : ℕ) (kx : List Bool) (j : ℕ) : ℕ := min (Nat.fromBitsLE (blockOf W kx j)) R

/-- The word of the scaled entry `M i j * 2^(R - k j)`. -/
def scaledStr (W N R : ℕ) (Mx kx : List Bool) (i j : ℕ) : List Bool :=
  wshl (blockOf W Mx (i * N + j)) (R - kOf W R kx j)

/-- The word of the Gram entry `∑_j M̃ a j * M̃ b j`. -/
def gramStr (W N R : ℕ) (Mx kx : List Bool) (a b : ℕ) : List Bool :=
  sumWords W (fun j => wmul (scaledStr W N R Mx kx a j) (scaledStr W N R Mx kx b j)) N

/-- The word of entry `(a, b)` of `[[M̃ M̃ᵀ, M̃], [M̃ᵀ, I]]`. -/
def projEntryStr (W m N R : ℕ) (Mx kx : List Bool) (a b : ℕ) : List Bool :=
  if a < m then (if b < m then gramStr W N R Mx kx a b else scaledStr W N R Mx kx a (b - m))
  else (if b < m then scaledStr W N R Mx kx b (a - m) else if a = b then word W 1 else word W 0)

/-- The matrix `[[M̃ M̃ᵀ, M̃], [M̃ᵀ, I]]`, stored. -/
def projStr (W m N R : ℕ) (Mx kx : List Bool) : List Bool :=
  (List.range ((m + N) * (m + N))).flatMap fun t =>
    fitTo W (projEntryStr W m N R Mx kx (t / (m + N)) (t % (m + N)))

/-- The matrix after `m` steps of fraction-free elimination. -/
def bareissOutStr (W m N R : ℕ) (Mx kx : List Bool) : List Bool :=
  loopN (bareissStrStep W (m + N)) m (projStr W m N R Mx kx)

/-- The trailing `N × N` block of a stored `(m + N) × (m + N)` matrix. -/
def qStr (W m N : ℕ) (Bx : List Bool) : List Bool :=
  (List.range (N * N)).flatMap fun t => blockOf W Bx ((m + t / N) * (m + N) + (m + t % N))

/-- The pivot after `m` steps of elimination on a stored `(m + N) × (m + N)` matrix. -/
def deltaStr (W m N : ℕ) (Bx : List Bool) : List Bool := pivotStr W (m + N) m Bx

/-- The first index of a largest stored count. -/
def argmaxStr (W N : ℕ) (cx : List Bool) : ℕ :=
  firstIdx (fun j => ∀ i < N, msb (wsub (blockOf W cx j) (blockOf W cx i)) = false) N

/-- The perceptron run of a round with stored exponents `kx`. -/
def percRunStr (W m N R T : ℕ) (Mx kx : List Bool) : List Bool :=
  percStrLoop W N T (qStr W m N (bareissOutStr W m N R Mx kx))
    (deltaStr W m N (bareissOutStr W m N R Mx kx))

/-- **One round on strings.** -/
def roundStrStep (W m N R T : ℕ) (Mx x : List Bool) : List Bool :=
  if headBit x = true then x
  else if headBit (percRunStr W m N R T Mx (x.drop 1)) = true then true :: x.drop 1
  else false :: incrStr W N (argmaxStr W N ((percRunStr W m N R T Mx (x.drop 1)).drop 1))
    (x.drop 1)

theorem length_roundStrStep {W m N R T : ℕ} (Mx : List Bool) {x : List Bool}
    (hx : x.length = 1 + N * W) : (roundStrStep W m N R T Mx x).length = 1 + N * W := by
  unfold roundStrStep
  split_ifs
  · exact hx
  · simp [hx]
    omega
  · simp [length_incrStr]
    omega

/-! ### Polynomial time -/

section Polytime

variable {W m N R T : List Bool → ℕ} {Mx X : List Bool → List Bool}

theorem kOf_unary {J : List Bool → ℕ} (hW : UnaryFn W) (hR : UnaryFn R) (hX : X ∈ FP)
    (hJ : UnaryFn J) : UnaryFn fun z => kOf (W z) (R z) (X z) (J z) :=
  UnaryFn.fromBitsLE_min (blockOf_mem_FP hW hX hJ) hR

theorem scaledStr_mem_FP {I J : List Bool → ℕ} (hW : UnaryFn W) (hN : UnaryFn N)
    (hR : UnaryFn R) (hM : Mx ∈ FP) (hX : X ∈ FP) (hI : UnaryFn I) (hJ : UnaryFn J) :
    (fun z => scaledStr (W z) (N z) (R z) (Mx z) (X z) (I z) (J z)) ∈ FP :=
  wshl_mem_FP (blockOf_mem_FP hW hM ((hI.mul hN).add hJ)) (hR.sub (kOf_unary hW hR hX hJ))

theorem length_scaledStr (W N R : ℕ) (Mx kx : List Bool) (i j : ℕ) :
    (scaledStr W N R Mx kx i j).length = W := by
  simp [scaledStr, length_wshl]

theorem gramStr_mem_FP {A B : List Bool → ℕ} (hW : UnaryFn W) (hN : UnaryFn N)
    (hR : UnaryFn R) (hM : Mx ∈ FP) (hX : X ∈ FP) (hA : UnaryFn A) (hB : UnaryFn B) :
    (fun z => gramStr (W z) (N z) (R z) (Mx z) (X z) (A z) (B z)) ∈ FP := by
  have hW' := hW.comp pairFst_mem_FP
  have hN' := hN.comp pairFst_mem_FP
  have hR' := hR.comp pairFst_mem_FP
  have hM' := mem_FP_comp pairFst_mem_FP hM
  have hX' := mem_FP_comp pairFst_mem_FP hX
  refine sumWords_mem_FP (e := fun z j => wmul (scaledStr (W z) (N z) (R z) (Mx z) (X z) (A z) j)
    (scaledStr (W z) (N z) (R z) (Mx z) (X z) (B z) j)) hW hN ?_ fun z j => by
      rw [length_wmul, length_scaledStr]
  exact wmul_mem_FP (scaledStr_mem_FP hW' hN' hR' hM' hX' (hA.comp pairFst_mem_FP) UnaryFn.idx)
    (scaledStr_mem_FP hW' hN' hR' hM' hX' (hB.comp pairFst_mem_FP) UnaryFn.idx)

theorem projEntryStr_mem_FP {A B : List Bool → ℕ} (hW : UnaryFn W) (hm : UnaryFn m)
    (hN : UnaryFn N) (hR : UnaryFn R) (hM : Mx ∈ FP) (hX : X ∈ FP) (hA : UnaryFn A)
    (hB : UnaryFn B) :
    (fun z => projEntryStr (W z) (m z) (N z) (R z) (Mx z) (X z) (A z) (B z)) ∈ FP := by
  have hs := fun {I J : List Bool → ℕ} (hI : UnaryFn I) (hJ : UnaryFn J) =>
    scaledStr_mem_FP hW hN hR hM hX hI hJ
  exact FPPred.ite_mem_FP (FPPred.lt hA hm)
    (FPPred.ite_mem_FP (FPPred.lt hB hm) (gramStr_mem_FP hW hN hR hM hX hA hB) (hs hA (hB.sub hm)))
    (FPPred.ite_mem_FP (FPPred.lt hB hm) (hs hB (hA.sub hm))
      (FPPred.ite_mem_FP (FPPred.eq hA hB) (WordFn.const hW 1) (WordFn.const hW 0)))

theorem projStr_mem_FP (hW : UnaryFn W) (hm : UnaryFn m) (hN : UnaryFn N) (hR : UnaryFn R)
    (hM : Mx ∈ FP) (hX : X ∈ FP) :
    (fun z => projStr (W z) (m z) (N z) (R z) (Mx z) (X z)) ∈ FP := by
  have hn := hm.add hN
  have hn' := hn.comp pairFst_mem_FP
  exact flatMap_range_mem_FP' (hn.mul hn) (fitTo_mem_FP (hW.comp pairFst_mem_FP)
    (projEntryStr_mem_FP (hW.comp pairFst_mem_FP) (hm.comp pairFst_mem_FP)
      (hN.comp pairFst_mem_FP) (hR.comp pairFst_mem_FP) (mem_FP_comp pairFst_mem_FP hM)
      (mem_FP_comp pairFst_mem_FP hX) (UnaryFn.idx.div hn') (UnaryFn.idx.mod hn')))

theorem length_projStr (W m N R : ℕ) (Mx kx : List Bool) :
    (projStr W m N R Mx kx).length = (m + N) * (m + N) * W :=
  length_flatMap_range_const _ _ _ fun _ => length_fitTo _ _

theorem bareissOutStr_mem_FP (hW : UnaryFn W) (hm : UnaryFn m) (hN : UnaryFn N)
    (hR : UnaryFn R) (hM : Mx ∈ FP) (hX : X ∈ FP) :
    (fun z => bareissOutStr (W z) (m z) (N z) (R z) (Mx z) (X z)) ∈ FP :=
  bareissStrLoop_mem_FP hW (hm.add hN) hm (projStr_mem_FP hW hm hN hR hM hX)
    fun _ => length_projStr _ _ _ _ _ _

theorem qStr_mem_FP {B : List Bool → List Bool} (hW : UnaryFn W) (hm : UnaryFn m)
    (hN : UnaryFn N) (hB : B ∈ FP) : (fun z => qStr (W z) (m z) (N z) (B z)) ∈ FP := by
  have hm' := hm.comp pairFst_mem_FP
  have hN' := hN.comp pairFst_mem_FP
  exact flatMap_range_mem_FP' (hN.mul hN) (blockOf_mem_FP (hW.comp pairFst_mem_FP)
    (mem_FP_comp pairFst_mem_FP hB) (((hm'.add (UnaryFn.idx.div hN')).mul (hm'.add hN')).add
      (hm'.add (UnaryFn.idx.mod hN'))))

theorem argmaxStr_unary (hW : UnaryFn W) (hN : UnaryFn N) (hX : X ∈ FP) :
    UnaryFn fun z => argmaxStr (W z) (N z) (X z) := by
  have hX' := mem_FP_comp ctx₂_mem_FP hX
  have hW' := hW.comp ctx₂_mem_FP
  have hlt : FPPred fun q => msb (wsub (blockOf (W (pairFst (pairFst q))) (X (pairFst (pairFst q)))
      (pairSnd (pairFst q)).length) (blockOf (W (pairFst (pairFst q)))
        (X (pairFst (pairFst q))) (pairSnd q).length)) = true :=
    FPPred.of_flag (msb_mem_FP (wsub_mem_FP (blockOf_mem_FP hW' hX' UnaryFn.idxOuter)
      (blockOf_mem_FP hW' hX' UnaryFn.idx)))
  exact UnaryFn.firstIdx_of_iff hN (FPPred.forall_lt (hN.comp pairFst_mem_FP) hlt.not)
    fun _ j hj => by simp

theorem percRunStr_mem_FP (hW : UnaryFn W) (hm : UnaryFn m) (hN : UnaryFn N) (hR : UnaryFn R)
    (hT : UnaryFn T) (hM : Mx ∈ FP) (hX : X ∈ FP) :
    (fun z => percRunStr (W z) (m z) (N z) (R z) (T z) (Mx z) (X z)) ∈ FP := by
  have hB := bareissOutStr_mem_FP hW hm hN hR hM hX
  exact percStrLoop_mem_FP hW hN hT (qStr_mem_FP hW hm hN hB)
    (pivotStr_mem_FP hW (hm.add hN) hm hB)

/-- **A round is polynomial-time.** -/
theorem roundStrStep_mem_FP (hW : UnaryFn W) (hm : UnaryFn m) (hN : UnaryFn N) (hR : UnaryFn R)
    (hT : UnaryFn T) (hM : Mx ∈ FP) (hX : X ∈ FP) :
    (fun z => roundStrStep (W z) (m z) (N z) (R z) (T z) (Mx z) (X z)) ∈ FP := by
  have hK : (fun z => (X z).drop 1) ∈ FP := drop_mem_FP hX (UnaryFn.const 1)
  have hP := percRunStr_mem_FP hW hm hN hR hT hM hK
  have hC : (fun z => (percRunStr (W z) (m z) (N z) (R z) (T z) (Mx z) ((X z).drop 1)).drop 1)
      ∈ FP := drop_mem_FP hP (UnaryFn.const 1)
  exact FPPred.ite_mem_FP (FPPred.of_flag (headBit_mem_FP hX)) hX
    (FPPred.ite_mem_FP (FPPred.of_flag (headBit_mem_FP hP))
      (mem_FP_comp hK (Cobham.cons_mem_FP true))
      (mem_FP_comp (incrStr_mem_FP hW hN (argmaxStr_unary hW hN hC) hK)
        (Cobham.cons_mem_FP false)))

end Polytime

/-! ### What a round computes -/

theorem kOf_vecStr {W R N j : ℕ} {k : ℕ → ℕ} (hj : j < N) (hk : k j ≤ R) (hR : R < 2 ^ W) :
    kOf W R (vecStr W (fun l => (k l : ℤ)) N) j = k j := by
  rw [kOf, blockOf_vecStr hj, word_natCast, Nat.fromBitsLE_toBitsLE (by omega)]
  exact min_eq_left hk

theorem scaledStr_eq {W N R m i j : ℕ} {M : ℕ → ℕ → ℤ} {k : ℕ → ℕ} (hi : i < m) (hj : j < N)
    (hk : k j ≤ R) (hR : R < 2 ^ W) :
    scaledStr W N R (matStr W M m N) (vecStr W (fun l => (k l : ℤ)) N) i j =
      word W (scaled M R k i j) := by
  rw [scaledStr, kOf_vecStr hj hk hR, blockOf_matStr hi hj, wshl_word]
  rfl

theorem gramStr_eq {W N R m a b : ℕ} {M : ℕ → ℕ → ℤ} {k : ℕ → ℕ} (ha : a < m) (hb : b < m)
    (hk : ∀ j < N, k j ≤ R) (hR : R < 2 ^ W) :
    gramStr W N R (matStr W M m N) (vecStr W (fun l => (k l : ℤ)) N) a b =
      word W (gram (scaled M R k) N a b) := by
  rw [gramStr, sumWords_eq (f := fun j => scaled M R k a j * scaled M R k b j) fun j hj => by
    rw [scaledStr_eq ha hj (hk j hj) hR, scaledStr_eq hb hj (hk j hj) hR, wmul_word], gram,
    ← Fin.sum_univ_eq_sum_range (fun j => scaled M R k a j * scaled M R k b j) N]

theorem projStr_eq {W m N R : ℕ} {M : ℕ → ℕ → ℤ} {k : ℕ → ℕ} (hk : ∀ j < N, k j ≤ R)
    (hR : R < 2 ^ W) :
    projStr W m N R (matStr W M m N) (vecStr W (fun l => (k l : ℤ)) N) =
      matStr W (projBlock (scaled M R k) m N) (m + N) (m + N) := by
  refine flatMap_range_eq_vecStr fun t ht => ?_
  have hn : 0 < m + N := by
    rcases Nat.eq_zero_or_pos (m + N) with h | h
    · simp [h] at ht
    · exact h
  have ha : t / (m + N) < m + N := (Nat.div_lt_iff_lt_mul hn).mpr ht
  have hb : t % (m + N) < m + N := Nat.mod_lt _ hn
  set a := t / (m + N)
  set b := t % (m + N)
  rw [projEntryStr]
  unfold projBlock
  split_ifs with h1 h2 h3 h4
  · rw [gramStr_eq h1 h2 hk hR, fitTo_word]
  · rw [scaledStr_eq h1 (by omega) (hk _ (by omega)) hR, fitTo_word]
  · rw [scaledStr_eq h3 (by omega) (hk _ (by omega)) hR, fitTo_word]
  · rw [fitTo_word]
  · rw [fitTo_word]

theorem qStr_eq {W m N : ℕ} {B : ℕ → ℕ → ℤ} :
    qStr W m N (matStr W B (m + N) (m + N)) = matStr W (fun a b => B (m + a) (m + b)) N N := by
  refine flatMap_range_eq_vecStr fun t ht => ?_
  have hn : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h] at ht
    · exact h
  have ha : t / N < N := (Nat.div_lt_iff_lt_mul hn).mpr ht
  have hb : t % N < N := Nat.mod_lt _ hn
  rw [blockOf_matStr (by omega) (by omega)]

theorem argmaxStr_eq {W N T : ℕ} {c : ℕ → ℕ} (hc : ∀ j, c j ≤ T) (hT : (T : ℤ) < 2 ^ (W - 1)) :
    argmaxStr W N (vecStr W (fun l => (c l : ℤ)) N) = argmaxIdx (fun j => (c j : ℤ)) N := by
  unfold argmaxStr argmaxIdx
  refine firstIdx_congr fun j hj => forall_congr' fun i => imp_congr_right fun hi => ?_
  rw [blockOf_vecStr hj, blockOf_vecStr hi, wsub_word, msb_word]
  · simp
  · unfold Fits
    have h1 := hc j
    have h2 := hc i
    rw [abs_lt]
    constructor <;> omega

/-- **One round on an encoding computes the round**, for a state with exponents at most `R`,
`M` with independent rows, the entries of `[[M̃ M̃ᵀ, M̃], [M̃ᵀ, I]]` at most `U`, and words long
enough for `(N T + 1) minorBound (m + N) U ^ 2` and for `T`. -/
theorem roundStrStep_percEnc {W m N R T U : ℕ} {M : ℕ → ℕ → ℤ} (hind : RowsIndep M m N)
    {s : Bool × (ℕ → ℕ)} (hk : ∀ j < N, s.2 j ≤ R) (hR : R < 2 ^ W)
    (hH : ∀ a < m + N, ∀ b < m + N, |projBlock (scaled M R s.2) m N a b| ≤ U)
    (hW : ((N * T + 1 : ℕ) : ℤ) * (minorBound (m + N) U : ℤ) ^ 2 < 2 ^ (W - 1))
    (hTW : (T : ℤ) < 2 ^ (W - 1)) :
    roundStrStep W m N R T (matStr W M m N) (percEnc W N s) =
      percEnc W N (chubRound m N M R T s) := by
  unfold roundStrStep chubRound
  rw [show headBit (percEnc W N s) = s.1 from rfl]
  by_cases hflag : s.1 = true
  · rw [ite_eq_left hflag, ite_eq_left hflag]
  rw [ite_eq_right hflag, ite_eq_right hflag]
  have hdrop : (percEnc W N s).drop 1 = vecStr W (fun j => (s.2 j : ℤ)) N := rfl
  rw [hdrop]
  -- the projection data
  set A := scaled M R s.2
  have hA : RowsIndep A m N := hind.scaled R s.2
  set H := projBlock A m N
  have hlead : ∀ l, 1 ≤ l → l < m → leadMinor H l ≠ 0 := fun l _ hl => by
    rw [leadMinor_projBlock hl.le]
    exact (gram_leadMinor_pos hA hl.le).ne'
  have hB1 : (1 : ℤ) ≤ minorBound (m + N) U := by exact_mod_cast one_le_minorBound _ _
  have hMB : (minorBound (m + N) U : ℤ) ^ 2 < 2 ^ (W - 1) := by
    refine lt_of_le_of_lt ?_ hW
    have : (1 : ℤ) ≤ ((N * T + 1 : ℕ) : ℤ) := by exact_mod_cast Nat.le_add_left 1 _
    nlinarith [sq_nonneg (minorBound (m + N) U : ℤ)]
  have hbar : bareissOutStr W m N R (matStr W M m N) (vecStr W (fun j => (s.2 j : ℤ)) N) =
      matStr W (bareiss H m).1 (m + N) (m + N) := by
    rw [bareissOutStr, projStr_eq hk hR]
    exact bareissStrLoop_eq (by omega) hH hlead hMB
  set B := roundBareiss m N M R s.2 with hBdef
  have hBH : B = bareiss H m := rfl
  have hQ : qStr W m N (bareissOutStr W m N R (matStr W M m N)
      (vecStr W (fun j => (s.2 j : ℤ)) N)) = matStr W (roundQ m B) N N := by
    rw [hbar, qStr_eq]
    rfl
  have hδ : deltaStr W m N (bareissOutStr W m N R (matStr W M m N)
      (vecStr W (fun j => (s.2 j : ℤ)) N)) = word W B.2 := by
    rw [hbar, deltaStr, pivotStr_matStr (by omega), ← bareiss_snd, hBH]
  -- the sizes of `Q` and `δ`
  obtain ⟨hz1, hz2⟩ := bareiss_int_eq_borderedMinor H m hlead
  have hδb : |B.2| ≤ minorBound (m + N) U := by
    rw [hBH, hz2]
    exact abs_leadMinor_le_minorBound (by omega) hH
  have hQb : ∀ a b, a < N → b < N → |roundQ m B a b| ≤ minorBound (m + N) U := fun a b ha hb => by
    rw [roundQ, hBH, hz1 _ _ (by omega) (by omega)]
    exact abs_borderedMinor_le_minorBound (by omega) (by omega) (by omega) hH
  have hfitP : ∀ c : ℕ → ℕ, (∀ j, c j ≤ T) → ∀ i < N, Fits W (B.2 * qmul N (roundQ m B) c i) :=
    fun c hc i hi => by
      unfold Fits
      have hq : |qmul N (roundQ m B) c i| ≤ N * T * minorBound (m + N) U := by
        unfold qmul
        calc |∑ j : Fin N, roundQ m B i j * (c j : ℤ)|
            ≤ ∑ j : Fin N, |roundQ m B i j * (c j : ℤ)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _j : Fin N, (minorBound (m + N) U : ℤ) * T := Finset.sum_le_sum fun j _ => by
              rw [abs_mul, Nat.abs_cast]
              exact mul_le_mul (hQb i j hi j.2) (by exact_mod_cast hc j) (by positivity)
                (by positivity)
          _ = N * T * minorBound (m + N) U := by simp; ring
      calc |B.2 * qmul N (roundQ m B) c i| = |B.2| * |qmul N (roundQ m B) c i| := abs_mul _ _
        _ ≤ minorBound (m + N) U * (N * T * minorBound (m + N) U) :=
            mul_le_mul hδb hq (abs_nonneg _) (by positivity)
        _ ≤ ((N * T + 1 : ℕ) : ℤ) * (minorBound (m + N) U : ℤ) ^ 2 := by push_cast; nlinarith
        _ < 2 ^ (W - 1) := hW
  have hperc : percRunStr W m N R T (matStr W M m N) (vecStr W (fun j => (s.2 j : ℤ)) N) =
      percEnc W N (perceptron N (roundQ m B) B.2 T) := by
    rw [percRunStr, hQ, hδ]
    exact percStrLoop_eq hfitP
  rw [hperc, show headBit (percEnc W N (perceptron N (roundQ m B) B.2 T)) =
    (perceptron N (roundQ m B) B.2 T).1 from rfl]
  split_ifs with hp
  · rfl
  · -- the counts are at most `T`
    have hcT : ∀ j, (perceptron N (roundQ m B) B.2 T).2 j ≤ T := by
      unfold perceptron
      have : ∀ r : ℕ, ∀ j, (loopN (fun _ => percStep N (roundQ m B) B.2) r
          (false, fun _ => 0)).2 j ≤ r := by
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
      exact fun j => this T j
    rw [show (percEnc W N (perceptron N (roundQ m B) B.2 T)).drop 1 =
      vecStr W (fun j => ((perceptron N (roundQ m B) B.2 T).2 j : ℤ)) N from rfl,
      argmaxStr_eq hcT hTW, incrStr_vecStr]
    rfl

end

end LinearProgramming
