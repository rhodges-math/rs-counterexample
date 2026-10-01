import Schubert.RS.Complexity.Parse
import Schubert.RS.Complexity.Instances
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Bitwise

/-!
# Writing integers in polynomial time

The polytope `P(a, b, c)` is written in the encoding of `Complexity/Instances.lean`: an integer
`v` as the pair of its sign `decide (v < 0)` and the binary digits of `|v|`. This file shows that
two kinds of integers can be written in polynomial time.

* Integers of polynomially bounded size (`IntFn`): both `v⁺` and `v⁻` are polynomial-time
  numbers in unary. They are closed under constants, sums, negation and case distinction on
  polynomial-time tests (`IntFn.encode_mem_FP`).
* Differences of binary numbers of equal width (`diffEncode_mem_FP`): the absolute value is
  computed in binary (`subBits`, a subtraction by complement and addition), and then written
  with its minimal binary expansion (`binEncode_mem_FP`).
-/

namespace Schubert.RS.Algorithms

open Complexity

noncomputable section

/-! ### Encodings of pairs, booleans and integers -/

theorem bitstringEncode_prod {α β : Type} [DataEncode α] [DataEncode β] (x : α) (y : β) :
    DataEncode.bitstringEncode (x, y) =
      false :: (DataEncode.bitstringEncode x ++ DataEncode.bitstringEncode y ++ [true]) := by
  rw [DataEncode.bitstringEncode_def, DataEncode_pair, Data.toBits_l]
  simp [DataEncode.bitstringEncode_def]

/-- An integer is written as its sign and the binary digits of its absolute value. -/
theorem bitstringEncode_int (v : ℤ) :
    DataEncode.bitstringEncode v =
      false :: (DataEncode.bitstringEncode (decide (v < 0)) ++
        DataEncode.bitstringEncode v.natAbs ++ [true]) :=
  bitstringEncode_prod (decide (v < 0)) v.natAbs

/-- `x ↦ 0 x y 1`: the brackets of a pair around two polynomial-time strings. -/
theorem bracket_mem_FP {x y : List Bool → List Bool} (hx : x ∈ FP) (hy : y ∈ FP) :
    (fun z => false :: (x z ++ y z ++ [true])) ∈ FP :=
  mem_FP_comp (Cobham.appendFn_mem_FP (Cobham.appendFn_mem_FP hx hy) (constFn_mem_FP [true]))
    (Cobham.cons_mem_FP false)

theorem boolEncode_mem_FP {p : List Bool → Prop} [DecidablePred p] (hp : FPPred p) :
    (fun z => DataEncode.bitstringEncode (decide (p z))) ∈ FP := by
  refine mem_FP_of_eq (FPPred.ite_mem_FP hp (constFn_mem_FP [false, false, true, true])
    (constFn_mem_FP [false, true])) fun z => ?_
  by_cases h : p z
  · simp [h, bitstringEncode_true]
  · simp [h, bitstringEncode_false]

/-! ### Integers of polynomial size -/

/-- An integer-valued function whose positive and negative parts are polynomial-time numbers. -/
def IntFn (v : List Bool → ℤ) : Prop :=
  UnaryFn (fun z => (v z).toNat) ∧ UnaryFn (fun z => (-v z).toNat)

namespace IntFn

variable {v w : List Bool → ℤ}

theorem of_eq (hv : IntFn v) (h : ∀ z, v z = w z) : IntFn w :=
  ⟨hv.1.of_eq fun z => by rw [h z], hv.2.of_eq fun z => by rw [h z]⟩

theorem const (c : ℤ) : IntFn fun _ => c :=
  ⟨UnaryFn.const _, UnaryFn.const _⟩

theorem ofNat {f : List Bool → ℕ} (hf : UnaryFn f) : IntFn fun z => (f z : ℤ) :=
  ⟨hf.of_eq fun z => by simp, (UnaryFn.const 0).of_eq fun z => by dsimp only; omega⟩

theorem neg (hv : IntFn v) : IntFn fun z => -v z :=
  ⟨hv.2, hv.1.of_eq fun z => by rw [neg_neg]⟩

theorem add (hv : IntFn v) (hw : IntFn w) : IntFn fun z => v z + w z :=
  ⟨((hv.1.add hw.1).sub (hv.2.add hw.2)).of_eq fun z => by dsimp only; omega,
    ((hv.2.add hw.2).sub (hv.1.add hw.1)).of_eq fun z => by dsimp only; omega⟩

theorem sub (hv : IntFn v) (hw : IntFn w) : IntFn fun z => v z - w z :=
  (hv.add hw.neg).of_eq fun z => by ring

theorem ite {p : List Bool → Prop} [DecidablePred p] (hp : FPPred p) (hv : IntFn v)
    (hw : IntFn w) : IntFn fun z => if p z then v z else w z :=
  ⟨(UnaryFn.ite hp hv.1 hw.1).of_eq fun z => by dsimp only; split_ifs <;> rfl,
    (UnaryFn.ite hp hv.2 hw.2).of_eq fun z => by dsimp only; split_ifs <;> rfl⟩

/-- The indicator of a polynomial-time test. -/
theorem ind {p : List Bool → Prop} [DecidablePred p] (hp : FPPred p) :
    IntFn fun z => if p z then (1 : ℤ) else 0 :=
  ite hp (const 1) (const 0)

/-- **Writing an integer of polynomial size is polynomial-time.** -/
theorem encode_mem_FP (hv : IntFn v) : (fun z => DataEncode.bitstringEncode (v z)) ∈ FP := by
  have hneg : FPPred fun z => v z < 0 :=
    (FPPred.lt (UnaryFn.const 0) hv.2).of_iff fun z => by omega
  have habs : UnaryFn fun z => (v z).natAbs := (hv.1.add hv.2).of_eq fun z => by omega
  refine mem_FP_of_eq (bracket_mem_FP (boolEncode_mem_FP hneg) (natEncode_mem_FP habs))
    fun z => ?_
  rw [bitstringEncode_int]

end IntFn

/-! ### Binary numbers -/

theorem getD_eq_testBit : ∀ (r : List Bool) (j : ℕ), r.getD j false = (binValLE r).testBit j
  | [], j => by simp [binValLE]
  | b :: w, 0 => by
    rw [binValLE_cons, Nat.testBit_zero]
    cases b <;> simp
  | b :: w, j + 1 => by
    rw [binValLE_cons, Nat.testBit_succ, List.getD_cons_succ, getD_eq_testBit w j]
    congr 1
    cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

/-- The first `size v` digits of a binary numeral of value `v` are the binary expansion of `v`. -/
theorem take_size_eq_bits (r : List Bool) : r.take (Nat.size (binValLE r)) = (binValLE r).bits := by
  have hsize : Nat.size (binValLE r) ≤ r.length := Nat.size_le.mpr (binValLE_lt r)
  apply List.ext_getElem
  · rw [List.length_take, Nat.size_eq_bits_len]
    omega
  · intro j h1 h2
    rw [List.getElem_take, ← List.getD_eq_getElem r false (by simp at h1; omega), getD_eq_testBit,
      Nat.testBit_eq_inth, List.getI_eq_getElem]

theorem size_binValLE_eq_card (r : List Bool) :
    Nat.size (binValLE r) = ((Finset.range r.length).filter fun j => 2 ^ j ≤ binValLE r).card := by
  have hsize : Nat.size (binValLE r) ≤ r.length := Nat.size_le.mpr (binValLE_lt r)
  have h : (Finset.range r.length).filter (fun j => 2 ^ j ≤ binValLE r) =
      Finset.range (Nat.size (binValLE r)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, ← Nat.lt_size]
    omega
  rw [h, Finset.card_range]

/-- The binary numeral `2^j` of width `W` (zero if `j ≥ W`). -/
def pow2Str (W j : ℕ) : List Bool := (List.range W).map fun t => decide (t = j)

@[simp] theorem length_pow2Str (W j : ℕ) : (pow2Str W j).length = W := by
  simp [pow2Str]

theorem binValLE_pow2Str {W j : ℕ} (hj : j < W) : binValLE (pow2Str W j) = 2 ^ j := by
  have h : pow2Str W j =
      (List.range W).map fun t => (List.replicate j false ++ [true]).getD t false := by
    simp only [pow2Str]
    congr 1
    funext t
    rcases lt_trichotomy t j with h | rfl | h
    · rw [List.getD_append _ _ _ _ (by simpa using h)]
      simp [List.getD_eq_getElem?_getD, h, h.ne]
    · rw [List.getD_append_right _ _ _ _ (by simp)]
      simp
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp only [decide_eq_false_iff_not]
      omega
  rw [h, binValLE_map_range_getD _ _ (by simp; omega), binValLE_replicate_false_append]
  simp [binValLE]

theorem pow2Str_mem_FP {W J : List Bool → ℕ} (hW : UnaryFn W) (hJ : UnaryFn J) :
    (fun z => pow2Str (W z) (J z)) ∈ FP :=
  bitwise_mem_FP (len := W) (b := fun x t => decide (t = J x)) (UnaryFn.mem_FP hW)
    (FPPred.flag_mem_FP (FPPred.eq UnaryFn.index hJ.lift)) fun x i => by
      simp [pairFst_pair, pairSnd_pair]

/-- **Writing a binary numeral's value is polynomial-time**: the minimal expansion is a prefix of
the numeral, of the length counted by comparisons with powers of two. -/
theorem binEncode_mem_FP {R : List Bool → List Bool} (hR : R ∈ FP) :
    (fun z => DataEncode.bitstringEncode (binValLE (R z))) ∈ FP := by
  have hRf : (fun w => R (pairFst w)) ∈ FP := mem_FP_comp pairFst_mem_FP hR
  have hP : (fun w => pow2Str (R (pairFst w)).length (pairSnd w).length) ∈ FP :=
    pow2Str_mem_FP (UnaryFn.length hRf) UnaryFn.index
  have hp : FPPred fun w =>
      ¬ binValLE (R (pairFst w)) < binValLE (pow2Str (R (pairFst w)).length (pairSnd w).length) :=
    FPPred.not (fpred_binValLE_lt hRf hP fun w => by simp)
  have hcount : UnaryFn fun z => Nat.size (binValLE (R z)) := by
    refine ((UnaryFn.length hR).count hp).of_eq fun z => ?_
    simp only [pairFst_pair, pairSnd_pair, List.length_replicate]
    rw [size_binValLE_eq_card]
    congr 1
    refine Finset.filter_congr fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [binValLE_pow2Str hj, not_lt]
  refine mem_FP_of_eq (encodeList_mem_FP (take_mem_FP hR hcount)) fun z => ?_
  rw [take_size_eq_bits]
  rfl

/-! ### Subtraction -/

/-- The complement of a binary numeral. -/
def complBits (u : List Bool) : List Bool := u.map not

theorem binValLE_complBits : ∀ u : List Bool,
    binValLE (complBits u) + binValLE u + 1 = 2 ^ u.length
  | [] => by simp [complBits, binValLE]
  | b :: w => by
    have ih := binValLE_complBits w
    simp only [complBits, List.map_cons] at ih ⊢
    rw [binValLE_cons, binValLE_cons, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

theorem complBits_mem_FP {U : List Bool → List Bool} (hU : U ∈ FP) :
    (fun z => complBits (U z)) ∈ FP := by
  have hG : (fun w => notBit [(U (pairFst w))[(pairSnd w).length]?.getD false]) ∈ FP :=
    notBitFn_mem_FP (getBit_mem_FP (mem_FP_comp pairFst_mem_FP hU) UnaryFn.index)
  refine mem_FP_of_eq (bitwise_mem_FP (len := fun z => (U z).length)
    (b := fun x t => !(U x)[t]?.getD false) (UnaryFn.length hU) hG fun x i => by
      simp [notBit_singleton]) fun z => ?_
  apply List.ext_getElem
  · simp [complBits]
  · intro i h1 h2
    have hi : i < (U z).length := by simpa [complBits] using h2
    simp [complBits, List.getElem?_eq_getElem hi]

@[simp] theorem length_complBits (u : List Bool) : (complBits u).length = u.length := by
  simp [complBits]

/-- Addition of two numerals of equal width, modulo `2 ^ width`. -/
theorem binValLE_addBits_mod (u v : List Bool) (h : v.length = u.length) :
    binValLE (addBits u v) = (binValLE u + binValLE v) % 2 ^ u.length := by
  have hk := addBitsLE_binValLE false u v h
  have hlt := binValLE_lt (addBitsLE false u v).2
  rw [addBitsLE_length] at hlt
  rw [addBits_eq u v h]
  simp only [Bool.toNat_false, Nat.add_zero] at hk
  rw [← hk]
  cases (addBitsLE false u v).1
  · simp only [Bool.toNat_false, Nat.zero_mul, Nat.add_zero]
    exact (Nat.mod_eq_of_lt hlt).symm
  · simp only [Bool.toNat_true, Nat.one_mul, Nat.add_mod_right]
    exact (Nat.mod_eq_of_lt hlt).symm

/-- `u − v` for numerals of equal width with `v ≤ u`: `u + (2^W − 1 − v) + 1` modulo `2^W`. -/
def subBits (u v : List Bool) : List Bool :=
  addBits (addBits u (complBits v)) (pow2Str u.length 0)

theorem binValLE_subBits (u v : List Bool) (h : v.length = u.length)
    (hle : binValLE v ≤ binValLE u) : binValLE (subBits u v) = binValLE u - binValLE v := by
  have hc := binValLE_complBits v
  have hU := binValLE_lt u
  rw [h] at hc
  have hlen1 : (complBits v).length = u.length := by rw [length_complBits, h]
  have hlen2 : (pow2Str u.length 0).length = (addBits u (complBits v)).length := by
    rw [length_pow2Str, addBits_length _ _ hlen1]
  rw [subBits, binValLE_addBits_mod _ _ hlen2, binValLE_addBits_mod _ _ hlen1,
    addBits_length _ _ hlen1]
  set P := 2 ^ u.length with hP
  rcases Nat.eq_zero_or_pos u.length with h0 | hpos
  · have hP1 : P = 1 := by rw [hP, h0, pow_zero]
    rw [hP1, Nat.mod_one]
    omega
  rw [binValLE_pow2Str hpos, pow_zero]
  rcases Nat.lt_or_ge (binValLE v) (binValLE u) with hlt | hge
  · have h1 : (binValLE u + binValLE (complBits v)) % P = binValLE u - binValLE v - 1 := by
      have he : binValLE u + binValLE (complBits v) = (binValLE u - binValLE v - 1) + P := by
        omega
      rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [h1, Nat.mod_eq_of_lt (by omega)]
    omega
  · have he : binValLE u = binValLE v := le_antisymm hge hle
    have h1 : (binValLE u + binValLE (complBits v)) % P = P - 1 :=
      Nat.mod_eq_of_lt (by omega) |>.trans (by omega)
    rw [h1, Nat.sub_add_cancel (Nat.one_le_two_pow), Nat.mod_self]
    omega

theorem subBits_mem_FP {U V : List Bool → List Bool} (hU : U ∈ FP) (hV : V ∈ FP) :
    (fun z => subBits (U z) (V z)) ∈ FP :=
  addBitsFn_mem_FP (addBitsFn_mem_FP hU (complBits_mem_FP hV))
    (pow2Str_mem_FP (UnaryFn.length hU) (UnaryFn.const 0))

/-- **Writing a difference of binary numerals of equal width is polynomial-time.** -/
theorem diffEncode_mem_FP {U V : List Bool → List Bool} (hU : U ∈ FP) (hV : V ∈ FP)
    (hlen : ∀ z, (V z).length = (U z).length) :
    (fun z => DataEncode.bitstringEncode ((binValLE (U z) : ℤ) - binValLE (V z))) ∈ FP := by
  have hlt : FPPred fun z => binValLE (U z) < binValLE (V z) := fpred_binValLE_lt hU hV hlen
  have hR : (fun z => if binValLE (U z) < binValLE (V z) then subBits (V z) (U z)
      else subBits (U z) (V z)) ∈ FP :=
    FPPred.ite_mem_FP hlt (subBits_mem_FP hV hU) (subBits_mem_FP hU hV)
  have hsign : FPPred fun z => ((binValLE (U z) : ℤ) - binValLE (V z)) < 0 :=
    hlt.of_iff fun z => by omega
  refine mem_FP_of_eq (bracket_mem_FP (boolEncode_mem_FP hsign) (binEncode_mem_FP hR))
    fun z => ?_
  have key : binValLE (if binValLE (U z) < binValLE (V z) then subBits (V z) (U z)
      else subBits (U z) (V z)) = ((binValLE (U z) : ℤ) - binValLE (V z)).natAbs := by
    by_cases h : binValLE (U z) < binValLE (V z)
    · rw [ite_eq_left h, binValLE_subBits _ _ (hlen z).symm h.le]
      omega
    · rw [ite_eq_right h, binValLE_subBits _ _ (hlen z) (not_lt.mp h)]
      omega
  rw [bitstringEncode_int, key]

end

end Schubert.RS.Algorithms
