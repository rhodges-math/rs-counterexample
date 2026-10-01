import Schubert.RS.Complexity.RecognitionSpec
import Complexitylib.Classes.P
import Complexitylib.Classes.PCP.Internal.DataScan
import Complexitylib.Classes.Containments.Internal.BinArith

/-!
# Reading encoded inputs in polynomial time

Polynomial-time access to the entries of an encoded triple `encodeTriple a b c`, and fixed-width
binary arithmetic on them.

* `childStr i s`: the encoding of the `i`-th entry of an encoded list (empty past its end), and
  `childNum s`, its number of entries.
* `numBits W s`: the `W` lowest binary digits, least significant first, of an encoded natural
  number.
* `valStr ℓ i z`: the `i`-th entry of the `ℓ`-th list of an encoded triple, and `psumStr ℓ k z`
  the sum of its first `k` entries, both in binary of the fixed width `width z = 2|z| + 2`.
* `inp d w`, `var e w`: the input and the bound variables of a context of nested bounded
  quantifiers, which complexitylib writes as `pair w (1^i)`.

Each comes with its polynomial-time computability. On valid encodings the binary values are the
entries and prefix sums themselves (`binValLE_valStr`, `binValLE_psumStr`): the width is large
enough that no sum overflows (`two_mul_total_lt`).
-/

namespace Schubert.RS.Algorithms

open Complexity

noncomputable section

/-! ### Contexts of bounded quantifiers -/

/-- The input inside `d` nested bounded quantifiers, which wrap it as `pair w (1^i)`. -/
def inp (d : ℕ) (w : List Bool) : List Bool := pairFst^[d] w

/-- The value of the `e`-th innermost bound variable, read in unary. -/
def var (e : ℕ) (w : List Bool) : ℕ := (pairSnd (pairFst^[e] w)).length

theorem inp_mem_FP (d : ℕ) : inp d ∈ FP := by
  induction d with
  | zero => exact id_mem_FP
  | succ d ih =>
    refine mem_FP_of_eq (mem_FP_comp pairFst_mem_FP ih) fun w => ?_
    simp only [inp, Function.comp_apply, Function.iterate_succ_apply]

theorem inp_length_le (d : ℕ) (w : List Bool) : (inp d w).length ≤ w.length := by
  induction d generalizing w with
  | zero => exact le_rfl
  | succ d ih =>
    simp only [inp, Function.iterate_succ_apply] at ih ⊢
    exact (ih _).trans (pairFst_length_le w)

theorem var_unary (e : ℕ) : UnaryFn (var e) :=
  UnaryFn.length (mem_FP_comp (inp_mem_FP e) pairSnd_mem_FP)

@[simp] theorem inp_zero (w : List Bool) : inp 0 w = w := rfl

@[simp] theorem inp_succ_pair (d : ℕ) (w y : List Bool) : inp (d + 1) (pair w y) = inp d w := by
  simp only [inp, Function.iterate_succ_apply, pairFst_pair]

@[simp] theorem var_zero_pair (w : List Bool) (i : ℕ) :
    var 0 (pair w (List.replicate i true)) = i := by
  simp only [var, Function.iterate_zero_apply, pairSnd_pair, List.length_replicate]

@[simp] theorem var_succ_pair (e : ℕ) (w y : List Bool) : var (e + 1) (pair w y) = var e w := by
  simp only [var, Function.iterate_succ_apply, pairFst_pair]

@[simp] theorem inp_pair_of_pos {d : ℕ} (hd : 0 < d) (w y : List Bool) :
    inp d (pair w y) = inp (d - 1) w := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hd
  simp

@[simp] theorem var_pair_of_pos {e : ℕ} (he : 0 < e) (w y : List Bool) :
    var e (pair w y) = var (e - 1) w := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt he
  simp

/-! ### Encoded lists -/

/-- An encoded list without its outer brackets. -/
def innerStr (s : List Bool) : List Bool := (s.drop 1).take (s.length - 2)

theorem innerStr_mem_FP {S : List Bool → List Bool} (hS : S ∈ FP) :
    (fun z => innerStr (S z)) ∈ FP :=
  take_mem_FP (drop_mem_FP hS (UnaryFn.const 1))
    (UnaryFn.sub (UnaryFn.length hS) (UnaryFn.const 2))

/-- The encoding of the `i`-th entry of an encoded list; empty past its end. -/
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

/-- The number of entries of an encoded list. -/
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

theorem childStr_bitstringEncode {α : Type} [DataEncode α] (L : List α) (i : ℕ) :
    childStr i (DataEncode.bitstringEncode L) =
      ((L[i]?).map DataEncode.bitstringEncode).getD [] := by
  rw [show DataEncode.bitstringEncode L = (Data.l (L.map DataEncode.encode)).toBits from rfl,
    childStr_toBits, List.getElem?_map, Option.map_map]
  rfl

theorem childNum_bitstringEncode {α : Type} [DataEncode α] (L : List α) :
    childNum (DataEncode.bitstringEncode L) = L.length := by
  rw [show DataEncode.bitstringEncode L = (Data.l (L.map DataEncode.encode)).toBits from rfl,
    childNum_toBits, List.length_map]

/-! ### Encoded natural numbers -/

/-- Binary digit `j` of an encoded natural number: its `j`-th child encodes a one with four
symbols and a zero with two. -/
def bitAt (j : ℕ) (s : List Bool) : Bool := decide (2 < (childStr j s).length)

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
    (FPPred.flag_mem_FP hp) fun x i => by simp [bitAt]

theorem bitAt_bitstringEncode (x j : ℕ) :
    bitAt j (DataEncode.bitstringEncode x) = x.bits.getD j false := by
  rw [show DataEncode.bitstringEncode x = DataEncode.bitstringEncode x.bits from rfl, bitAt,
    childStr_bitstringEncode, List.getD_eq_getElem?_getD]
  cases x.bits[j]? with
  | none => rfl
  | some b => cases b <;> simp [length_bitstringEncode_bool]

theorem bitAt_nil (j : ℕ) : bitAt j [] = false := by
  simp [bitAt, childStr_nil]

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

theorem binValLE_numBits_bitstringEncode {W x : ℕ} (hx : x.size ≤ W) :
    binValLE (numBits W (DataEncode.bitstringEncode x)) = x := by
  have h : numBits W (DataEncode.bitstringEncode x) =
      (List.range W).map fun j => x.bits.getD j false := by
    simp only [numBits, bitAt_bitstringEncode]
  rw [h, binValLE_map_range_getD _ _ (by rw [Nat.size_eq_bits_len]; exact hx), binValLE_bits]

theorem binValLE_numBits_nil (W : ℕ) : binValLE (numBits W []) = 0 := by
  have : numBits W [] = List.replicate W false := by
    apply List.ext_getElem <;> simp [numBits, bitAt_nil]
  rw [this, binValLE_replicate_false]

/-- The value of an entry of an encoded list of numbers. -/
theorem binValLE_numBits_childStr {W : ℕ} (L : List ℕ) (i : ℕ) (hL : ∀ x ∈ L, x.size ≤ W) :
    binValLE (numBits W (childStr i (DataEncode.bitstringEncode L))) = L.getD i 0 := by
  rw [childStr_bitstringEncode, List.getD_eq_getElem?_getD]
  cases h : L[i]? with
  | none => exact binValLE_numBits_nil W
  | some x =>
    exact binValLE_numBits_bitstringEncode (hL x (List.mem_of_getElem? h))

/-! ### Entries and prefix sums of an encoded triple -/

/-- The working width `2|z| + 2` of the binary arithmetic on the input `z`. -/
def width (z : List Bool) : ℕ := 2 * z.length + 2

theorem width_unary {Z : List Bool → List Bool} (hZ : Z ∈ FP) : UnaryFn fun w => width (Z w) :=
  UnaryFn.add (UnaryFn.mul (UnaryFn.const 2) (UnaryFn.length hZ)) (UnaryFn.const 2)

/-- Entry `i` of list `ℓ` of the encoded triple `z`, in binary of width `width z`. -/
def valStr (ℓ i : ℕ) (z : List Bool) : List Bool := numBits (width z) (childStr i (childStr ℓ z))

@[simp] theorem length_valStr (ℓ i : ℕ) (z : List Bool) : (valStr ℓ i z).length = width z :=
  length_numBits _ _

theorem valStr_mem_FP {Z : List Bool → List Bool} {I : List Bool → ℕ} (hZ : Z ∈ FP)
    (hI : UnaryFn I) (ℓ : ℕ) : (fun w => valStr ℓ (I w) (Z w)) ∈ FP :=
  numBits_mem_FP (width_unary hZ) (childStr_mem_FP hI (childStr_mem_FP (UnaryFn.const ℓ) hZ))

/-- The running prefix sums of list `ℓ`: one addition per symbol of the counter. -/
def psumAux (ℓ : ℕ) (z : List Bool) : List Bool → List Bool
  | [] => List.replicate (width z) false
  | _ :: t => addBits (psumAux ℓ z t) (valStr ℓ t.length z)

/-- The sum of the first `k` entries of list `ℓ` of the encoded triple `z`, in binary. -/
def psumStr (ℓ k : ℕ) (z : List Bool) : List Bool := psumAux ℓ z (List.replicate k true)

theorem length_psumAux (ℓ : ℕ) (z : List Bool) : ∀ t, (psumAux ℓ z t).length = width z
  | [] => by simp [psumAux]
  | _ :: t => by
    rw [psumAux, addBits_length _ _ (by rw [length_valStr, length_psumAux ℓ z t]),
      length_psumAux ℓ z t]

@[simp] theorem length_psumStr (ℓ k : ℕ) (z : List Bool) : (psumStr ℓ k z).length = width z :=
  length_psumAux _ _ _

theorem psumStr_mem_FP {Z : List Bool → List Bool} {K : List Bool → ℕ} (hZ : Z ∈ FP)
    (hZlen : ∀ w, (Z w).length ≤ w.length) (hK : UnaryFn K) (ℓ : ℕ) :
    (fun w => psumStr ℓ (K w) (Z w)) ∈ FP := by
  have hB : (fun v => addBits (pairSnd (pairFst v))
      (valStr ℓ (pairSnd v).length (Z (pairFst (pairFst v))))) ∈ FP :=
    addBitsFn_mem_FP (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
      (valStr_mem_FP (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) hZ)
        UnaryFn.index ℓ)
  have hE : (fun w => List.replicate (width (Z w)) false) ∈ FP :=
    UnaryFn.replicate_mem_FP (width_unary hZ) false
  have hbound : PolyBound fun n => 2 * n + 2 :=
    ⟨Polynomial.C 2 * Polynomial.X + Polynomial.C 2, fun n => by simp⟩
  exact recFold_mem_FP_of_bound (g := fun w t => psumAux ℓ (Z w) t) hB hB hE id_mem_FP
    (UnaryFn.mem_FP hK) (fun _ => rfl) (fun _ _ => by simp [psumAux])
    (fun _ _ => by simp [psumAux]) hbound fun w t _ => by
      rw [length_psumAux, width]
      have := hZlen w
      omega

/-! ### Values on valid inputs -/

/-- The `ℓ`-th list of the triple (empty for `ℓ ≥ 3`). -/
def listOf (a b c : List ℕ) (ℓ : ℕ) : List ℕ := [a, b, c].getD ℓ []

@[simp] theorem listOf_zero (a b c : List ℕ) : listOf a b c 0 = a := rfl
@[simp] theorem listOf_one (a b c : List ℕ) : listOf a b c 1 = b := rfl
@[simp] theorem listOf_two (a b c : List ℕ) : listOf a b c 2 = c := rfl

theorem childStr_encodeTriple (a b c : List ℕ) {ℓ : ℕ} (hℓ : ℓ < 3) :
    childStr ℓ (encodeTriple a b c) = DataEncode.bitstringEncode (listOf a b c ℓ) := by
  rw [encodeTriple, childStr_bitstringEncode]
  rcases ℓ with _ | _ | _ | ℓ
  · rfl
  · rfl
  · rfl
  · omega

theorem childNum_encodeTriple (a b c : List ℕ) {ℓ : ℕ} (hℓ : ℓ < 3) :
    childNum (childStr ℓ (encodeTriple a b c)) = (listOf a b c ℓ).length := by
  rw [childStr_encodeTriple a b c hℓ, childNum_bitstringEncode]

/-- The sum of all entries of the triple. -/
def total (a b c : List ℕ) : ℕ := (a ++ b ++ c).sum

theorem sum_add_one_le_two_pow (l : List ℕ) :
    l.sum + 1 ≤ 2 ^ (l.map fun x => (DataEncode.bitstringEncode x).length).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.sum_cons, List.map_cons, pow_add]
    have hx : x + 1 ≤ 2 ^ (DataEncode.bitstringEncode x).length := by
      have h1 := Nat.lt_size_self x
      have h2 := size_mul_two_le x
      have h3 : 2 ^ x.size ≤ 2 ^ (DataEncode.bitstringEncode x).length :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hA := Nat.one_le_two_pow (n := (DataEncode.bitstringEncode x).length)
    have hB := Nat.one_le_two_pow
      (n := (l.map fun x => (DataEncode.bitstringEncode x).length).sum)
    nlinarith

theorem two_mul_total_lt (a b c : List ℕ) :
    2 * total a b c < 2 ^ width (encodeTriple a b c) := by
  have h := sum_add_one_le_two_pow (a ++ b ++ c)
  have hlen := length_encodeTriple a b c
  have h2 : 2 ^ ((a ++ b ++ c).map fun x => (DataEncode.bitstringEncode x).length).sum ≤
      2 ^ (encodeTriple a b c).length := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ width (encodeTriple a b c) = 4 * (2 ^ (encodeTriple a b c).length) ^ 2 := by
    unfold width
    ring
  rw [h3, total]
  nlinarith

theorem size_le_width (a b c : List ℕ) (ℓ : ℕ) :
    ∀ x ∈ listOf a b c ℓ, x.size ≤ width (encodeTriple a b c) := by
  intro x hx
  have hmem : x ∈ a ++ b ++ c := by
    rcases ℓ with _ | _ | _ | ℓ
    · simp_all
    · simp_all
    · simp_all
    · simp [listOf, List.getD_eq_getElem?_getD] at hx
  have h1 := size_mul_two_le x
  have h2 : (DataEncode.bitstringEncode x).length ≤
      ((a ++ b ++ c).map fun x => (DataEncode.bitstringEncode x).length).sum :=
    List.le_sum_of_mem (List.mem_map_of_mem hmem)
  have h3 := length_encodeTriple a b c
  rw [width]
  omega

theorem binValLE_valStr (a b c : List ℕ) {ℓ : ℕ} (hℓ : ℓ < 3) (i : ℕ) :
    binValLE (valStr ℓ i (encodeTriple a b c)) = (listOf a b c ℓ).getD i 0 := by
  rw [valStr, childStr_encodeTriple a b c hℓ]
  exact binValLE_numBits_childStr _ _ (size_le_width a b c ℓ)

theorem psum_succ (x : List ℕ) (k : ℕ) : psum x (k + 1) = psum x k + x.getD k 0 :=
  Finset.sum_range_succ _ _

theorem psum_eq_sum_take (x : List ℕ) (k : ℕ) : psum x k = (x.take k).sum := by
  induction k with
  | zero => simp [psum]
  | succ k ih =>
    rw [psum_succ, ih, List.take_add_one, List.sum_append, List.getD_eq_getElem?_getD]
    cases x[k]? <;> simp

theorem psum_le_sum (x : List ℕ) (k : ℕ) : psum x k ≤ x.sum := by
  rw [psum_eq_sum_take]
  exact (List.take_sublist k x).sum_le_sum fun _ _ => Nat.zero_le _

theorem getD_le_sum (x : List ℕ) (i : ℕ) : x.getD i 0 ≤ x.sum := by
  rw [List.getD_eq_getElem?_getD]
  cases h : x[i]? with
  | none => exact Nat.zero_le _
  | some y => exact List.le_sum_of_mem (List.mem_of_getElem? h)

theorem sum_listOf_le (a b c : List ℕ) (ℓ : ℕ) : (listOf a b c ℓ).sum ≤ total a b c := by
  rcases ℓ with _ | _ | _ | ℓ
  · show a.sum ≤ _
    simp only [total, List.sum_append]; omega
  · show b.sum ≤ _
    simp only [total, List.sum_append]; omega
  · show c.sum ≤ _
    simp only [total, List.sum_append]; omega
  · simp [listOf, List.getD_eq_getElem?_getD]

theorem binValLE_psumStr (a b c : List ℕ) {ℓ : ℕ} (hℓ : ℓ < 3) (k : ℕ) :
    binValLE (psumStr ℓ k (encodeTriple a b c)) = psum (listOf a b c ℓ) k := by
  have hT := two_mul_total_lt a b c
  have hS := sum_listOf_le a b c ℓ
  induction k with
  | zero => simp [psumStr, psumAux, binValLE_replicate_false, psum]
  | succ k ih =>
    have hstep : psumStr ℓ (k + 1) (encodeTriple a b c) =
        addBits (psumStr ℓ k (encodeTriple a b c)) (valStr ℓ k (encodeTriple a b c)) := by
      simp [psumStr, List.replicate_succ, psumAux]
    have hk1 := psum_le_sum (listOf a b c ℓ) (k + 1)
    rw [hstep, binValLE_addBits _ _ (by simp), ih, binValLE_valStr a b c hℓ, ← psum_succ]
    rw [ih, binValLE_valStr a b c hℓ, ← psum_succ, length_psumStr]
    omega

/-- Sums of two binary values of the working width do not overflow when they are at most twice
the total of the triple. -/
theorem binValLE_addBits_of_le (a b c : List ℕ) (u v : List Bool)
    (hu : u.length = width (encodeTriple a b c)) (hv : v.length = width (encodeTriple a b c))
    (h : binValLE u + binValLE v ≤ 2 * total a b c) :
    binValLE (addBits u v) = binValLE u + binValLE v := by
  have hT := two_mul_total_lt a b c
  exact binValLE_addBits u v (by rw [hu, hv]) (by rw [hu]; omega)

/-! ### Comparisons -/

/-- Comparing two binary values of equal width is a polynomial-time test. -/
theorem fpred_binValLE_lt {X Y : List Bool → List Bool} (hX : X ∈ FP) (hY : Y ∈ FP)
    (hlen : ∀ z, (Y z).length = (X z).length) :
    FPPred fun z => binValLE (X z) < binValLE (Y z) := by
  have hflag : (fun z => [(ltFlag (X z) (Y z)).headD false]) ∈ FP := by
    refine mem_FP_of_eq (ltFlagFn_mem_FP hX hY) fun z => ?_
    rw [ltFlag_eq _ _ (hlen z)]
    rfl
  refine FPPred.of_iff (FPPred.of_flag hflag) fun z => ?_
  rw [← ltFlag_eq_true_iff _ _ (hlen z), ltFlag_eq _ _ (hlen z)]
  simp

end

end Schubert.RS.Algorithms
