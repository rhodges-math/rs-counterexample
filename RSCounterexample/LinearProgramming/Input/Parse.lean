import RSCounterexample.LinearProgramming.Words.Div
import Complexitylib.Classes.PCP.Internal.DataScan
import Complexitylib.Encoding.DataEncode

/-!
# Reading encoded data in polynomial time

The inputs are serialized `Data` trees (`Complexity.Data.toBits`): a list node is `false`, the
serializations of its children, and `true`. This file reads such encodings in polynomial time:

* `LinearProgramming.childStr i s`: the serialization of child `i` of an encoded list (empty past
  its end), and `LinearProgramming.childNum s`, the number of children (both via complexitylib's
  `Complexity.DataScan`);
* `LinearProgramming.numBits W s`: the `W` lowest binary digits of an encoded natural number;
* `LinearProgramming.intWordStr W s`: the word of width `W` of an encoded integer, given as its
  sign and the binary digits of its absolute value (`LinearProgramming.intData`).

Missing children read as empty strings, and an empty string reads as the integer `0`
(`LinearProgramming.intWordStr_nil`). So reading a coefficient past the end of a row gives `0`,
just as `List.getD` does.

## Main definitions

* `LinearProgramming.childStr`, `LinearProgramming.childNum`, `LinearProgramming.numBits`.
* `LinearProgramming.intData`: an integer as `Data`.
* `LinearProgramming.intWordStr`: reading an encoded integer into a word.

## Main results

* `LinearProgramming.childStr_toBits`, `LinearProgramming.childNum_toBits`,
  `LinearProgramming.numBits_toBits`, `LinearProgramming.intWordStr_intData`: what is read.
* `LinearProgramming.childStr_mem_FP`, `LinearProgramming.childNum_unary`,
  `LinearProgramming.numBits_mem_FP`, `LinearProgramming.intWordStr_mem_FP`: polynomial time.
-/

namespace LinearProgramming

open Complexity

noncomputable section

/-! ### Children of encoded lists -/

/-- An encoded list without its outer brackets. -/
def innerStr (s : List Bool) : List Bool := (s.drop 1).take (s.length - 2)

theorem innerStr_mem_FP {S : List Bool → List Bool} (hS : S ∈ FP) :
    (fun z => innerStr (S z)) ∈ FP :=
  take_mem_FP (drop_mem_FP hS (UnaryFn.const 1))
    (UnaryFn.sub (UnaryFn.length hS) (UnaryFn.const 2))

/-- The serialization of child `i` of an encoded list; empty past its end. -/
def childStr (i : ℕ) (s : List Bool) : List Bool :=
  DataScan.childOf DataScan.scanPoly (DataScan.scanArg i (innerStr s))

theorem childStr_mem_FP {I : List Bool → ℕ} {S : List Bool → List Bool} (hI : UnaryFn I)
    (hS : S ∈ FP) : (fun z => childStr (I z) (S z)) ∈ FP := by
  have h := DataScan.scanArg_mem_FP (UnaryFn.mem_FP hI) (innerStr_mem_FP hS)
  refine mem_FP_of_eq (mem_FP_comp h (DataScan.childOf_mem_FP DataScan.scanPoly)) fun z => ?_
  simp only [Function.comp_apply, List.length_replicate, childStr]

theorem childStr_toBits (i : ℕ) (xs : List Data) :
    childStr i (Data.l xs).toBits = ((xs[i]?).map Data.toBits).getD [] := by
  rw [childStr, innerStr, DataScan.inner_toBits, DataScan.child_flatten]

theorem childStr_nil (i : ℕ) : childStr i [] = [] := by
  have h := DataScan.child_flatten i []
  simp only [List.map_nil, List.flatten_nil, List.getElem?_nil, Option.map_none,
    Option.getD_none] at h
  simpa [childStr, innerStr] using h

/-- The number of children of an encoded list. -/
def childNum (s : List Bool) : ℕ :=
  (DataScan.childCount DataScan.scanPoly (DataScan.scanArg 0 (innerStr s))).length

theorem childNum_unary {S : List Bool → List Bool} (hS : S ∈ FP) :
    UnaryFn fun z => childNum (S z) := by
  have h := DataScan.scanArg_mem_FP (UnaryFn.mem_FP (UnaryFn.const 0)) (innerStr_mem_FP hS)
  refine UnaryFn.of_eq (UnaryFn.length (mem_FP_comp h
    (DataScan.childCount_mem_FP DataScan.scanPoly))) fun z => ?_
  simp only [Function.comp_apply, List.length_replicate, childNum]

theorem childNum_toBits (xs : List Data) : childNum (Data.l xs).toBits = xs.length := by
  rw [childNum, innerStr, DataScan.inner_toBits, DataScan.childCount_flatten,
    List.length_replicate]

/-! ### Booleans and natural numbers -/

/-- The boolean of an encoded boolean: `true` is serialized with four symbols, `false` with
two. -/
def flagOf (s : List Bool) : Bool := decide (2 < s.length)

theorem flagOf_toBits (b : Bool) : flagOf (DataEncode.encode b).toBits = b := by
  cases b <;> simp [flagOf, DataEncode.encode, Data.toBits_l]

theorem flagOf_nil : flagOf [] = false := rfl

theorem flagOf_mem_FP {S : List Bool → List Bool} (hS : S ∈ FP) :
    (fun z => [flagOf (S z)]) ∈ FP :=
  (FPPred.lt (UnaryFn.const 2) (UnaryFn.length hS)).flag_mem_FP

/-- Binary digit `j` of an encoded natural number. -/
def bitAt (j : ℕ) (s : List Bool) : Bool := flagOf (childStr j s)

/-- The `W` lowest binary digits, least significant first, of an encoded natural number. -/
def numBits (W : ℕ) (s : List Bool) : List Bool := (List.range W).map fun j => bitAt j s

@[simp] theorem length_numBits (W : ℕ) (s : List Bool) : (numBits W s).length = W := by
  simp [numBits]

theorem numBits_mem_FP {W : List Bool → ℕ} {S : List Bool → List Bool} (hW : UnaryFn W)
    (hS : S ∈ FP) : (fun z => numBits (W z) (S z)) ∈ FP := by
  have hp : FPPred fun w => 2 < (childStr (pairSnd w).length (S (pairFst w))).length :=
    FPPred.lt (UnaryFn.const 2)
      (UnaryFn.length (childStr_mem_FP UnaryFn.index (mem_FP_comp pairFst_mem_FP hS)))
  exact bitwise_mem_FP (len := W) (b := fun x j => bitAt j (S x)) (UnaryFn.mem_FP hW)
    (FPPred.flag_mem_FP hp) fun x i => by simp [bitAt, flagOf]

theorem bitAt_toBits_nat (x j : ℕ) :
    bitAt j (DataEncode.encode x).toBits = x.bits.getD j false := by
  rw [show DataEncode.encode x = Data.l (x.bits.map DataEncode.encode) from rfl, bitAt,
    childStr_toBits, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases x.bits[j]? with
  | none => rfl
  | some b => exact flagOf_toBits b

theorem bitAt_nil (j : ℕ) : bitAt j [] = false := by
  simp [bitAt, childStr_nil, flagOf_nil]

theorem binValLE_map_range_getD :
    ∀ (l : List Bool) (W : ℕ), l.length ≤ W →
      binValLE ((List.range W).map fun j => l.getD j false) = binValLE l
  | [], W, _ => by
    have : ((List.range W).map fun j => ([] : List Bool).getD j false) =
        List.replicate W false := by
      apply List.ext_getElem <;> simp
    rw [this, binValLE_replicate_false]
    rfl
  | b :: l, W, h => by
    obtain ⟨W, rfl⟩ : ∃ W', W = W' + 1 := ⟨W - 1, by simp at h; omega⟩
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, binValLE_cons, binValLE_cons]
    have ih := binValLE_map_range_getD l W (by simp at h; omega)
    have hf : ((fun j => (b :: l).getD j false) ∘ Nat.succ) = fun j => l.getD j false := by
      funext j
      simp
    rw [hf, ih]
    simp

/-- **Reading an encoded natural number** below `2 ^ W` gives its binary expansion of length
`W`. -/
theorem numBits_toBits {W x : ℕ} (hx : x < 2 ^ W) :
    numBits W (DataEncode.encode x).toBits = Nat.toBitsLE W x := by
  have h : numBits W (DataEncode.encode x).toBits =
      (List.range W).map fun j => x.bits.getD j false := by
    simp only [numBits, bitAt_toBits_nat]
  rw [eq_toBitsLE_iff hx, h]
  refine ⟨by simp, ?_⟩
  rw [binValLE_map_range_getD _ _ (by rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr hx),
    binValLE_bits]

theorem numBits_nil (W : ℕ) : numBits W [] = Nat.toBitsLE W 0 := by
  rw [toBitsLE_zero]
  apply List.ext_getElem <;> simp [numBits, bitAt_nil]

/-! ### Integers -/

/-- The integer `v` as `Data`: its sign and the binary digits of `|v|`. -/
def intData (v : ℤ) : Data :=
  Data.l [DataEncode.encode (decide (v < 0)), DataEncode.encode v.natAbs]

/-- The word of width `W` of an encoded integer: the binary digits of the absolute value, negated
when the sign is set. -/
def intWordStr (W : ℕ) (s : List Bool) : List Bool :=
  Cobham.selectHead [flagOf (childStr 0 s)] (wneg (numBits W (childStr 1 s)))
    (numBits W (childStr 1 s))

/-- **Reading an encoded integer** whose absolute value is below `2 ^ W` gives its word. -/
theorem intWordStr_intData {W : ℕ} {v : ℤ} (hv : v.natAbs < 2 ^ W) :
    intWordStr W (intData v).toBits = word W v := by
  rw [intWordStr, intData, childStr_toBits, childStr_toBits]
  simp only [List.getElem?_cons_zero, Option.map_some, Option.getD_some,
    List.getElem?_cons_succ, flagOf_toBits]
  rw [numBits_toBits hv, ← word_natCast, selectHead_single]
  by_cases h : v < 0
  · rw [ite_eq_left (by simpa using h), wneg_word]
    congr 1
    omega
  · rw [ite_eq_right (by simpa using h)]
    congr 1
    omega

theorem intWordStr_nil (W : ℕ) : intWordStr W [] = word W 0 := by
  rw [intWordStr, childStr_nil, childStr_nil, flagOf_nil, selectHead_single, numBits_nil]
  simp only [Bool.false_eq_true, ite_false]
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, word_natCast]

theorem intWordStr_mem_FP {W : List Bool → ℕ} {S : List Bool → List Bool} (hW : UnaryFn W)
    (hS : S ∈ FP) : (fun z => intWordStr (W z) (S z)) ∈ FP := by
  have hc0 := childStr_mem_FP (UnaryFn.const 0) hS
  have hn := numBits_mem_FP hW (childStr_mem_FP (UnaryFn.const 1) hS)
  exact Cobham.selectHeadFn_mem_FP (flagOf_mem_FP hc0) (wneg_mem_FP hn) hn

end

end LinearProgramming
