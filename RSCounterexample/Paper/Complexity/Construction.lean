import RSCounterexample.Paper.Complexity.PolytopeEncode

/-!
# Constructing the polytope `P(a, b, c)` in polynomial time

Theorem 1.4 (construction): the polytope `P(a, b, c)` (`Quiver.Flat.quiverPolytope`) can be
written down in time polynomial in the binary length of the input (`quiverPolytope_construction`).

The input string `z` determines a positional quiver `posStr z` whose data are read with the
polynomial-time tools of `Parse.lean`: the length `n = |c|`, the starts of the intervals of the
canonical partition (binary comparisons of adjacent entries), their lengths, the numbers of
arrows (comparisons between starts) and the weights `ν_x = c_x − a_x − b_x` (binary differences).
On the encoding of a triple it is the canonical quiver of the triple (`posStr_encodeTriple`), and
its polytope is written in polynomial time by `PolytopeData.polytope_encode_mem_FP`.
-/

namespace Schubert.RS.Algorithms

open Complexity Schubert.RS.Quiver.Flat

noncomputable section

/-! ### The data read from the input -/

/-- The length `n` of the third list. -/
def nStr (z : List Bool) : ℕ := childNum (childStr 2 z)

/-- Entry `i` of list `ℓ` is below entry `j`, compared in binary. -/
def ltStr (ℓ i j : ℕ) (z : List Bool) : Prop := binValLE (valStr ℓ i z) < binValLE (valStr ℓ j z)

instance (ℓ i j : ℕ) (z : List Bool) : Decidable (ltStr ℓ i j z) := Nat.decLt _ _

/-- The position `i` starts an interval of the canonical partition. -/
def isStartStr (z : List Bool) (i : ℕ) : Bool :=
  decide (i = 0) || (decide (0 < i) && (decide (ltStr 0 (i - 1) i z) ||
    decide (ltStr 1 (i - 1) i z) || decide (ltStr 2 i (i - 1) z)))

/-- The length of the interval starting at `i`. -/
def blockDimStr (z : List Bool) (i : ℕ) : ℕ :=
  ((List.range (nStr z - (i + 1))).filter fun t =>
    (List.range (t + 1)).all fun s => !isStartStr z (i + 1 + s)).length + 1

/-- The comparison weight of the positions `i` and `j`. -/
def cmpStr (z : List Bool) (i j : ℕ) : ℤ :=
  (if ltStr 0 i j z then 1 else 0) + (if ltStr 1 i j z then 1 else 0) +
    (if ltStr 2 j i z then 1 else 0) - 1

/-- The number of arrows between the intervals starting at `i < j`. -/
def arrowCountStr (z : List Bool) (i j : ℕ) : ℕ :=
  if isStartStr z i && isStartStr z j && decide (i < j) then (cmpStr z i j).toNat else 0

/-- The residual `ν_x = c_x − (a_x + b_x)`, read in binary. -/
def nuStr (z : List Bool) (x : ℕ) : ℤ :=
  (binValLE (valStr 2 x z) : ℤ) - binValLE (addBits (valStr 0 x z) (valStr 1 x z))

/-- The positional quiver read from the input. -/
def posStr (z : List Bool) : PositionalQuiver where
  n := nStr z
  isStart := isStartStr z
  blockDim := blockDimStr z
  arrowCount := arrowCountStr z
  weight i l := nuStr z (i + blockDimStr z i - 1 - l)

/-! ### On the encoding of a triple -/

section Valid

variable (a b c : List ℕ)

theorem nStr_encodeTriple : nStr (encodeTriple a b c) = c.length :=
  childNum_encodeTriple a b c (ℓ := 2) (by norm_num)

theorem ltStr_encodeTriple {ℓ : ℕ} (hℓ : ℓ < 3) (i j : ℕ) :
    ltStr ℓ i j (encodeTriple a b c) ↔ entry (listOf a b c ℓ) i < entry (listOf a b c ℓ) j := by
  rw [ltStr, binValLE_valStr a b c hℓ, binValLE_valStr a b c hℓ]
  rfl

theorem isStartStr_encodeTriple : isStartStr (encodeTriple a b c) = isStart a b c := by
  funext i
  simp only [isStartStr, isStart, riseAt, ltStr_encodeTriple a b c (by norm_num : 0 < 3),
    ltStr_encodeTriple a b c (by norm_num : 1 < 3), ltStr_encodeTriple a b c (by norm_num : 2 < 3),
    listOf_zero, listOf_one, listOf_two]

theorem blockDimStr_encodeTriple : blockDimStr (encodeTriple a b c) = blockDim a b c := by
  funext i
  simp only [blockDimStr, blockDim, nStr_encodeTriple, isStartStr_encodeTriple]

theorem cmpStr_encodeTriple (i j : ℕ) : cmpStr (encodeTriple a b c) i j = cmpAt a b c i j := by
  simp only [cmpStr, cmpAt, ltStr_encodeTriple a b c (by norm_num : 0 < 3),
    ltStr_encodeTriple a b c (by norm_num : 1 < 3), ltStr_encodeTriple a b c (by norm_num : 2 < 3),
    listOf_zero, listOf_one, listOf_two]

theorem arrowCountStr_encodeTriple : arrowCountStr (encodeTriple a b c) = arrowCount a b c := by
  funext i j
  simp only [arrowCountStr, arrowCount, isStartStr_encodeTriple, cmpStr_encodeTriple]

theorem nuStr_encodeTriple (x : ℕ) : nuStr (encodeTriple a b c) x = nu a b c x := by
  have h0 := binValLE_valStr a b c (ℓ := 0) (by norm_num) x
  have h1 := binValLE_valStr a b c (ℓ := 1) (by norm_num) x
  have h2 := binValLE_valStr a b c (ℓ := 2) (by norm_num) x
  have hle : (listOf a b c 0).getD x 0 + (listOf a b c 1).getD x 0 ≤ 2 * total a b c := by
    have ha := getD_le_sum (listOf a b c 0) x
    have hb := getD_le_sum (listOf a b c 1) x
    have hsa := sum_listOf_le a b c 0
    have hsb := sum_listOf_le a b c 1
    omega
  rw [nuStr, binValLE_addBits_of_le a b c _ _ (by simp) (by simp) (by rw [h0, h1]; exact hle),
    h0, h1, h2]
  simp only [nu, entry, listOf_zero, listOf_one, listOf_two]
  push_cast
  ring

/-- **On the encoding of a triple, the quiver read from the input is the canonical quiver.** -/
theorem posStr_encodeTriple : posStr (encodeTriple a b c) = positionalOf a b c := by
  simp only [posStr, positionalOf, nStr_encodeTriple, isStartStr_encodeTriple,
    blockDimStr_encodeTriple, arrowCountStr_encodeTriple, nuStr_encodeTriple]

end Valid

/-! ### The data are polynomial-time -/

theorem card_filter_range (p : ℕ → Prop) [DecidablePred p] (N : ℕ) :
    ((Finset.range N).filter p).card = ((List.range N).filter fun i => decide (p i)).length := by
  rw [Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
    Multiset.coe_card]

section Polytime

variable {X : List Bool → List Bool} (hX : X ∈ FP) {I J : List Bool → ℕ} (hI : UnaryFn I)
  (hJ : UnaryFn J)

include hX

theorem nStr_at : UnaryFn fun u => nStr (X u) :=
  childNum_unary (childStr_mem_FP (UnaryFn.const 2) hX)

include hI hJ in
theorem ltStr_at (ℓ : ℕ) : FPPred fun u => ltStr ℓ (I u) (J u) (X u) :=
  fpred_binValLE_lt (valStr_mem_FP hX hI ℓ) (valStr_mem_FP hX hJ ℓ) fun u => by simp

include hI in
theorem isStartStr_at : FPPred fun u => isStartStr (X u) (I u) = true := by
  have hI' : UnaryFn fun u => I u - 1 := hI.sub (UnaryFn.const 1)
  refine ((FPPred.eq hI (UnaryFn.const 0)).or ((FPPred.lt (UnaryFn.const 0) hI).and
    (((ltStr_at hX hI' hI 0).or (ltStr_at hX hI' hI 1)).or (ltStr_at hX hI hI' 2)))).of_iff
    fun u => ?_
  simp [isStartStr]

include hI in
theorem blockDimStr_at : UnaryFn fun u => blockDimStr (X u) (I u) := by
  have hXc : (fun w => X (pairFst w)) ∈ FP := mem_FP_comp pairFst_mem_FP hX
  have hXcc : (fun w => X (pairFst (pairFst w))) ∈ FP :=
    mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) hX
  -- the test at `pair (pair u (1^t)) (1^s)`: no start at `i + 1 + s`
  have hs : FPPred fun w => ¬ isStartStr (X (pairFst (pairFst w)))
      (I (pairFst (pairFst w)) + 1 + (pairSnd w).length) = true :=
    FPPred.not (isStartStr_at hXcc (((hI.lift.lift).add (UnaryFn.const 1)).add UnaryFn.index))
  -- the test at `pair u (1^t)`: no start at `i + 1 + s` for `s ≤ t`
  have ht : FPPred fun w => ∀ s < (pairSnd w).length + 1,
      ¬ isStartStr (X (pairFst w)) (I (pairFst w) + 1 + s) = true :=
    (FPPred.forall_lt (UnaryFn.index.add (UnaryFn.const 1)) hs).of_iff fun w => by
      simp only [pairFst_pair, pairSnd_pair, List.length_replicate]
  have hcount := (((nStr_at hX).sub (hI.add (UnaryFn.const 1))).count ht).add (UnaryFn.const 1)
  refine hcount.of_eq fun u => ?_
  rw [card_filter_range, blockDimStr]
  congr 2
  apply List.filter_congr
  intro t _
  rw [Bool.eq_iff_iff, decide_eq_true_iff, List.all_eq_true]
  simp only [pairFst_pair, pairSnd_pair, List.length_replicate, List.mem_range]
  constructor
  · intro h s hs
    simpa using h s hs
  · intro h s hs
    simpa using h s hs

include hI hJ in
theorem cmpStr_at : IntFn fun u => cmpStr (X u) (I u) (J u) :=
  ((((IntFn.ind (ltStr_at hX hI hJ 0)).add (IntFn.ind (ltStr_at hX hI hJ 1))).add
    (IntFn.ind (ltStr_at hX hJ hI 2))).sub (IntFn.const 1)).of_eq fun _ => rfl

include hI hJ in
theorem arrowCountStr_at : UnaryFn fun u => arrowCountStr (X u) (I u) (J u) :=
  (UnaryFn.ite (((isStartStr_at hX hI).and (isStartStr_at hX hJ)).and (FPPred.lt hI hJ))
    (cmpStr_at hX hI hJ).1 (UnaryFn.const 0)).of_eq fun u => by
    simp only [arrowCountStr, Bool.and_eq_true, decide_eq_true_eq]

include hI in
theorem nuStr_encode_mem_FP :
    (fun u => DataEncode.bitstringEncode (nuStr (X u) (I u))) ∈ FP :=
  diffEncode_mem_FP (valStr_mem_FP hX hI 2)
    (addBitsFn_mem_FP (valStr_mem_FP hX hI 0) (valStr_mem_FP hX hI 1))
    fun u => by rw [addBits_length _ _ (by simp)]; simp

include hI in
theorem nuStr_neg_encode_mem_FP :
    (fun u => DataEncode.bitstringEncode (-nuStr (X u) (I u))) ∈ FP :=
  mem_FP_of_eq (diffEncode_mem_FP
    (addBitsFn_mem_FP (valStr_mem_FP hX hI 0) (valStr_mem_FP hX hI 1)) (valStr_mem_FP hX hI 2)
    fun u => by rw [addBits_length _ _ (by simp)]; simp) fun u => by
      rw [nuStr, neg_sub]

end Polytime

/-- The data of the quiver read from the input are polynomial-time. -/
theorem polytopeData_posStr : PolytopeData posStr where
  n := nStr_at id_mem_FP
  isStart := isStartStr_at pairFst_mem_FP UnaryFn.index
  blockDim := blockDimStr_at pairFst_mem_FP UnaryFn.index
  arrowCount := arrowCountStr_at (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
    (UnaryFn.length (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)) UnaryFn.index
  weight := by
    have hZ : (fun w => pairFst (pairFst w)) ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
    have hi : UnaryFn fun w => (pairSnd (pairFst w)).length :=
      UnaryFn.length (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
    exact nuStr_encode_mem_FP hZ
      (((hi.add (blockDimStr_at hZ hi)).sub (UnaryFn.const 1)).sub UnaryFn.index)
  weightNeg := by
    have hZ : (fun w => pairFst (pairFst w)) ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
    have hi : UnaryFn fun w => (pairSnd (pairFst w)).length :=
      UnaryFn.length (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
    exact nuStr_neg_encode_mem_FP hZ
      (((hi.add (blockDimStr_at hZ hi)).sub (UnaryFn.const 1)).sub UnaryFn.index)

/-- **Theorem 1.4 (construction): the polytope `P(a, b, c)` can be written in polynomial time.**
Some polynomial-time function maps the encoding of every triple of lists `a, b, c` of natural
numbers (in binary) to the encoding of `quiverPolytope a b c`: its dimension and its rows, each a
list of integer coefficients and an integer right-hand side. -/
theorem quiverPolytope_construction :
    ∃ f ∈ FP, ∀ a b c : List ℕ,
      f (encodeTriple a b c) = DataEncode.bitstringEncode (quiverPolytope a b c) :=
  ⟨_, polytopeData_posStr.polytope_encode_mem_FP, fun a b c => by
    simp only [posStr_encodeTriple]
    rfl⟩

end

end Schubert.RS.Algorithms
