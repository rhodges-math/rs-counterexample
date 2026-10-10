import RSCounterexample.LinearProgramming.Algorithm.Bounds
import RSCounterexample.LinearProgramming.Input.System

/-!
# Feasibility of linear inequalities is decidable in polynomial time

**Main theorem** (`LinearProgramming.exists_mem_FP_feasible`). Some polynomial-time function on
bitstrings accepts exactly the encodings (`LinearProgramming.encodeSystem`) of the finite systems
`A x ≤ b` with integer coefficients that have a rational solution
(`LinearProgramming.SystemFeasible`). Polynomial time is complexitylib's `Complexity.FP`:
deterministic multi-tape Turing machines running in time `O(nᵈ)`.

The algorithm (`LinearProgramming.decideStr`) reads the system from its encoding and builds the
homogeneous matrix `[2ᴱ A | −2ᴱ A | −(2ᴱ b + 1) | I]` as words. It then runs `R` rounds of the
projection-and-rescaling algorithm, all in exact integer arithmetic on words of a fixed width:
fraction-free elimination for the projection, the counting perceptron, and rescaling. All
parameters are explicit polynomials in the input length (`LinearProgramming.pW` and the others).

Polynomial time holds for all strings, whatever they encode
(`LinearProgramming.decideStr_mem_FP`). Correctness on encodings combines: the data are read
correctly (`LinearProgramming.homStr_encodeSystem`); every round on strings computes the round of
the algorithm, since all numbers fit their words (`LinearProgramming.roundStrStep_percEnc`,
`LinearProgramming.pW_spec`); and the algorithm decides feasibility
(`LinearProgramming.decideFeasible_iff`, `LinearProgramming.systemFeasible_iff`).

Feasibility of rational linear programs in polynomial time is due to L. G. Khachiyan,
*A polynomial algorithm in linear programming*, Dokl. Akad. Nauk SSSR 244 (1979). The algorithm
here is a version of S. Chubanov's projection-and-rescaling algorithm, *A polynomial projection
algorithm for linear feasibility problems*, Math. Program. 153 (2015).

## Main definitions

* `LinearProgramming.decideStr`: the decision procedure on bitstrings.

## Main results

* `LinearProgramming.decideStr_mem_FP`: it is polynomial-time.
* `LinearProgramming.decideStr_encodeSystem`: it decides feasibility.
* `LinearProgramming.exists_mem_FP_feasible`: the main theorem.
-/

namespace LinearProgramming

open Complexity

noncomputable section

/-! ### The procedure on strings -/

/-- The word of entry `(i, j)` of the homogeneous matrix `[2ᴱ A | −2ᴱ A | −(2ᴱ b + 1) | I]`,
read from the encoded system `z`. -/
def homEntryStr (W n E : ℕ) (z : List Bool) (i j : ℕ) : List Bool :=
  if j < n then wshl (aWordStr W z i j) E
  else if j < n + n then wneg (wshl (aWordStr W z i (j - n)) E)
  else if j = n + n then wneg (wadd (wshl (bWordStr W z i) E) (word W 1))
  else if j - (n + n + 1) = i then word W 1 else word W 0

/-- The word width for the input `z`. -/
def parW (z : List Bool) : ℕ := pW (mOf z) (nOf z) z.length

/-- The perturbation exponent for the input `z`. -/
def parE (z : List Bool) : ℕ := pE (mOf z) (nOf z) z.length

/-- The number of columns of the homogeneous matrix for the input `z`. -/
def parN (z : List Bool) : ℕ := pN (mOf z) (nOf z)

/-- The number of rounds for the input `z`. -/
def parR (z : List Bool) : ℕ := pR (mOf z) (nOf z) z.length

/-- The number of perceptron steps for the input `z`. -/
def parT (z : List Bool) : ℕ := pT (mOf z) (nOf z)

/-- The homogeneous matrix of the system encoded by `z`, stored as words. -/
def homStr (z : List Bool) : List Bool :=
  (List.range (mOf z * parN z)).flatMap fun t =>
    fitTo (parW z) (homEntryStr (parW z) (nOf z) (parE z) z (t / parN z) (t % parN z))

/-- The state after all rounds. -/
def finalStr (z : List Bool) : List Bool :=
  loopN (fun _ => roundStrStep (parW z) (mOf z) (parN z) (parR z) (parT z) (homStr z)) (parR z)
    (percEnc (parW z) (parN z) (false, fun _ => 0))

/-- **The decision procedure on bitstrings**: the flag after all rounds. -/
def decideStr (z : List Bool) : List Bool := [headBit (finalStr z)]

/-! ### Polynomial time -/

theorem parN_unary : UnaryFn parN :=
  (((nOf_unary.add nOf_unary).add (UnaryFn.const 1)).add mOf_unary).of_eq fun _ => rfl

theorem parE_unary : UnaryFn parE := by
  have hL : UnaryFn fun z : List Bool => z.length := UnaryFn.length id_mem_FP
  have hk : UnaryFn fun z => nOf z + nOf z + (mOf z + 1) :=
    (nOf_unary.add nOf_unary).add (mOf_unary.add (UnaryFn.const 1))
  exact (((hk.mul hk).add (hk.mul (mOf_unary.add ((UnaryFn.const 2).mul
    (hL.add (UnaryFn.const 1)))))).add (UnaryFn.const 1)).of_eq fun _ => rfl

theorem parR_unary : UnaryFn parR := by
  have hL : UnaryFn fun z : List Bool => z.length := UnaryFn.length id_mem_FP
  have hN2 := parN_unary.add parN_unary
  have hK : UnaryFn fun z => pK (mOf z) (nOf z) z.length :=
    ((hN2.mul hN2).add (hN2.mul ((mOf_unary.add parN_unary).add ((UnaryFn.const 2).mul
      ((parE_unary.add hL).add (UnaryFn.const 2)))))).of_eq fun _ => rfl
  exact ((parN_unary.mul (hK.add (UnaryFn.const 1))).add (UnaryFn.const 1)).of_eq fun _ => rfl

theorem parT_unary : UnaryFn parT :=
  (((UnaryFn.const 4).mul (parN_unary.pow_const 3)).add (UnaryFn.const 1)).of_eq fun _ => rfl

theorem parW_unary : UnaryFn parW := by
  have hL : UnaryFn fun z : List Bool => z.length := UnaryFn.length id_mem_FP
  have hA : UnaryFn fun z => pA (mOf z) (nOf z) z.length :=
    (((parE_unary.add hL).add (UnaryFn.const 1)).add parR_unary).of_eq fun _ => rfl
  have hH : UnaryFn fun z => pH (mOf z) (nOf z) z.length :=
    (((UnaryFn.const 2).mul hA).add parN_unary).of_eq fun _ => rfl
  have hs := (mOf_unary.add parN_unary).add (UnaryFn.const 1)
  have hMB : UnaryFn fun z => pMB (mOf z) (nOf z) z.length :=
    ((hs.mul hs).add (hs.mul (hH.add (UnaryFn.const 1)))).of_eq fun _ => rfl
  exact ((((((UnaryFn.const 2).mul hMB).add (parN_unary.mul parT_unary)).add parT_unary).add
    parR_unary).add hL |>.add (UnaryFn.const 2)).of_eq fun _ => rfl

theorem homEntryStr_mem_FP {W n E I J : List Bool → ℕ} {Z : List Bool → List Bool}
    (hW : UnaryFn W) (hn : UnaryFn n) (hE : UnaryFn E) (hZ : Z ∈ FP) (hI : UnaryFn I)
    (hJ : UnaryFn J) : (fun y => homEntryStr (W y) (n y) (E y) (Z y) (I y) (J y)) ∈ FP := by
  have ha := fun {J' : List Bool → ℕ} (hJ' : UnaryFn J') => aWordStr_mem_FP hW hZ hI hJ'
  exact FPPred.ite_mem_FP (FPPred.lt hJ hn) (wshl_mem_FP (ha hJ) hE)
    (FPPred.ite_mem_FP (FPPred.lt hJ (hn.add hn)) (wneg_mem_FP (wshl_mem_FP (ha (hJ.sub hn)) hE))
      (FPPred.ite_mem_FP (FPPred.eq hJ (hn.add hn))
        (wneg_mem_FP (wadd_mem_FP (wshl_mem_FP (bWordStr_mem_FP hW hZ hI) hE)
          (WordFn.const hW 1)))
        (FPPred.ite_mem_FP (FPPred.eq (hJ.sub ((hn.add hn).add (UnaryFn.const 1))) hI)
          (WordFn.const hW 1) (WordFn.const hW 0))))

theorem homStr_mem_FP : homStr ∈ FP := by
  have hN' := parN_unary.comp pairFst_mem_FP
  have hW' := parW_unary.comp pairFst_mem_FP
  exact flatMap_range_mem_FP' (mOf_unary.mul parN_unary) (fitTo_mem_FP hW'
    (homEntryStr_mem_FP hW' (nOf_unary.comp pairFst_mem_FP) (parE_unary.comp pairFst_mem_FP)
      pairFst_mem_FP (UnaryFn.idx.div hN') (UnaryFn.idx.mod hN')))

theorem finalStr_mem_FP : finalStr ∈ FP := by
  have hM : (fun q => homStr (pairFst (pairFst q))) ∈ FP := by
    have h := mem_FP_comp ctx₂_mem_FP homStr_mem_FP
    rw [Function.comp_def] at h
    exact h
  have hX : (fun q => pairSnd (pairFst q)) ∈ FP := by
    have h := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
    exact h
  have hstep : (fun q => roundStrStep (parW (pairFst (pairFst q))) (mOf (pairFst (pairFst q)))
      (parN (pairFst (pairFst q))) (parR (pairFst (pairFst q))) (parT (pairFst (pairFst q)))
      (homStr (pairFst (pairFst q))) (pairSnd (pairFst q))) ∈ FP :=
    roundStrStep_mem_FP (parW_unary.comp ctx₂_mem_FP) (mOf_unary.comp ctx₂_mem_FP)
      (parN_unary.comp ctx₂_mem_FP) (parR_unary.comp ctx₂_mem_FP) (parT_unary.comp ctx₂_mem_FP)
      hM hX
  have hzero : WordFn (fun y => parW (pairFst y)) fun _ => 0 :=
    WordFn.zero (parW_unary.comp pairFst_mem_FP)
  have hvec : (fun z => vecStr (parW z) (fun _ => 0) (parN z)) ∈ FP :=
    vecStr_mem_FP (f := fun _ _ => 0) parN_unary hzero
  have hinit : (fun z => percEnc (parW z) (parN z) (false, fun _ => 0)) ∈ FP := by
    refine mem_FP_of_eq (mem_FP_comp hvec (Cobham.cons_mem_FP false)) fun z => ?_
    simp [percEnc]
  have hℓ : UnaryFn fun z => 1 + parN z * parW z :=
    (UnaryFn.const 1).add (parN_unary.mul parW_unary)
  exact loopN_mem_FP (step := fun z _ x =>
      roundStrStep (parW z) (mOf z) (parN z) (parR z) (parT z) (homStr z) x)
    (init := fun z => percEnc (parW z) (parN z) (false, fun _ => 0)) (K := parR)
    (ℓ := fun z => 1 + parN z * parW z) hstep hinit parR_unary hℓ
    (fun z _ _ hx => length_roundStrStep (homStr z) hx) fun _ => length_percEnc _ _ _

/-- **The decision procedure is polynomial-time.** -/
theorem decideStr_mem_FP : decideStr ∈ FP := headBit_mem_FP finalStr_mem_FP

/-! ### Correctness -/

theorem homStr_encodeSystem (dim : ℕ) (rows : List (List ℤ × ℤ)) :
    homStr (encodeSystem dim rows) = matStr (parW (encodeSystem dim rows))
      (homEntry (effDim dim rows) (sysA rows) (sysB rows) (parE (encodeSystem dim rows)))
      rows.length (parN (encodeSystem dim rows)) := by
  have hm : mOf (encodeSystem dim rows) = rows.length := mOf_encodeSystem dim rows
  have hn : nOf (encodeSystem dim rows) = effDim dim rows := nOf_encodeSystem dim rows
  have hLW : (encodeSystem dim rows).length ≤ parW (encodeSystem dim rows) :=
    (pW_spec _ _ _).2.2.2
  unfold homStr
  rw [hm, hn]
  refine flatMap_range_eq_vecStr fun t ht => ?_
  have hN : 0 < parN (encodeSystem dim rows) := by unfold parN pN; omega
  have hi : t / parN (encodeSystem dim rows) < rows.length := (Nat.div_lt_iff_lt_mul hN).mpr ht
  have ha := fun j => aWordStr_encodeSystem (W := parW (encodeSystem dim rows)) (j := j) hi hLW
  have hb := bWordStr_encodeSystem (W := parW (encodeSystem dim rows)) hi hLW
  unfold homEntryStr homEntry
  split_ifs
  · rw [ha, wshl_word, fitTo_word, mul_comm]
  · rw [ha, wshl_word, wneg_word, fitTo_word, mul_comm]
  · rw [hb, wshl_word, wadd_word, wneg_word, fitTo_word, mul_comm]
  · rw [fitTo_word]
  · rw [fitTo_word]

/-- Incrementing one count raises the sum by at most one. -/
theorem sum_incr_le {N jj : ℕ} (c : ℕ → ℕ) :
    ∑ j : Fin N, (if (j : ℕ) = jj then c j + 1 else c j) ≤ ∑ j : Fin N, c j + 1 := by
  have h1 : ∀ j : Fin N, (if (j : ℕ) = jj then c j + 1 else c j) =
      c j + if (j : ℕ) = jj then 1 else 0 := fun j => by split_ifs <;> rfl
  rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_add_distrib]
  apply Nat.add_le_add_left
  rw [Fin.sum_univ_eq_sum_range (fun i => if i = jj then 1 else 0) N,
    Finset.sum_ite_eq' (Finset.range N) jj (fun _ => 1)]
  split_ifs <;> simp

/-- The exponents grow by at most one per round. -/
theorem sum_chubRound_le {m N : ℕ} {M : ℕ → ℕ → ℤ} {R T : ℕ} (s : Bool × (ℕ → ℕ)) :
    ∑ j : Fin N, (chubRound m N M R T s).2 j ≤ ∑ j : Fin N, s.2 j + 1 := by
  unfold chubRound
  split_ifs
  · exact Nat.le_succ _
  · exact Nat.le_succ _
  · exact sum_incr_le s.2

theorem sum_loopN_chubRound_le {m N : ℕ} {M : ℕ → ℕ → ℤ} {R T : ℕ} (r : ℕ) :
    ∑ j : Fin N, (loopN (fun _ => chubRound m N M R T) r (false, fun _ => 0)).2 j ≤ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [loopN_succ]
    exact (sum_chubRound_le _).trans (by omega)

/-- **The decision procedure decides feasibility** of encoded systems. -/
theorem decideStr_encodeSystem (dim : ℕ) (rows : List (List ℤ × ℤ)) :
    decideStr (encodeSystem dim rows) = [true] ↔ SystemFeasible dim rows := by
  have hm : mOf (encodeSystem dim rows) = rows.length := mOf_encodeSystem dim rows
  have hn : nOf (encodeSystem dim rows) = effDim dim rows := nOf_encodeSystem dim rows
  obtain ⟨-, -, -, hAsize, hbsize⟩ := encodeSystem_size dim rows
  -- the data and the parameters
  set m := rows.length
  set n := effDim dim rows
  set L := (encodeSystem dim rows).length
  set A := sysA rows
  set b := sysB rows
  set N := pN m n
  set E := pE m n L
  set R := pR m n L
  set T := pT m n
  set W := pW m n L
  set M := homEntry n A b E
  have hpar : parW (encodeSystem dim rows) = W ∧ parE (encodeSystem dim rows) = E ∧
      parN (encodeSystem dim rows) = N ∧ parR (encodeSystem dim rows) = R ∧
      parT (encodeSystem dim rows) = T := by
    simp only [parW, parE, parN, parR, parT, hm, hn]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨hW, hE, hN, hR, hT⟩ := hpar
  have hA : ∀ i < m, ∀ j < n, |A i j| ≤ ((2 ^ L : ℕ) : ℤ) := fun i _ j _ => by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast (hAsize i j).le
  have hb : ∀ i < m, |b i| ≤ ((2 ^ L : ℕ) : ℤ) := fun i _ => by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast (hbsize i).le
  have hM : ∀ i < m, ∀ j < N, |M i j| ≤ 2 ^ E * (2 ^ L + 1) := fun i hi j hj => by
    have := abs_homEntry_le (A := A) (b := b) E hA hb i hi j hj
    exact_mod_cast this
  obtain ⟨hWfit, hTfit, hRfit, -⟩ := pW_spec m n L
  -- the rounds on strings compute the rounds of the algorithm
  have hloop : finalStr (encodeSystem dim rows) =
      percEnc W N (loopN (fun _ => chubRound m N M R T) R (false, fun _ => 0)) := by
    unfold finalStr
    rw [homStr_encodeSystem, hm, hW, hE, hN, hR, hT]
    refine loopN_semiconj (percEnc W N) _ _ _ R fun r hr => ?_
    have hk : ∀ j < N, (loopN (fun _ => chubRound m N M R T) r (false, fun _ => 0)).2 j ≤ R :=
      fun j hj => by
        have h1 := sum_loopN_chubRound_le (m := m) (N := N) (M := M) (R := R) (T := T) r
        have h2 := Finset.single_le_sum (f := fun l : Fin N =>
          (loopN (fun _ => chubRound m N M R T) r (false, fun _ => 0)).2 l)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨j, hj⟩)
        simp only at h2
        omega
    exact roundStrStep_percEnc (U := 2 ^ pH m n L) (rowsIndep_homEntry m n A b E) hk hRfit
      (abs_projBlock_le hM _) hWfit hTfit
  -- the flag is the answer of the decision procedure
  have hdec : decideStr (encodeSystem dim rows) = [decideFeasible m n A b E R T] := by
    rw [decideStr, hloop]
    rfl
  rw [hdec, List.cons.injEq, and_iff_left rfl, decideFeasible_iff (U := 2 ^ L) (E := E)
    (K := pK m n L) (R := R) (T := T) Nat.one_le_two_pow hA hb (pE_spec m n L) (pK_spec m n L)
    (pR_spec m n L) le_rfl, systemFeasible_iff]

/-- **Feasibility of systems of linear inequalities with integer coefficients is decidable in
polynomial time.** Some polynomial-time function accepts exactly the encodings of the systems
that have a rational solution. -/
theorem exists_mem_FP_feasible :
    ∃ f ∈ FP, ∀ (dim : ℕ) (rows : List (List ℤ × ℤ)),
      f (encodeSystem dim rows) = [true] ↔ SystemFeasible dim rows :=
  ⟨decideStr, decideStr_mem_FP, decideStr_encodeSystem⟩

end

end LinearProgramming
