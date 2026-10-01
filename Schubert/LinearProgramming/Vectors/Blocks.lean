import Schubert.LinearProgramming.Words.Div

/-!
# Vectors of words

A vector of `ℓ` integers is stored as the words of its entries, one after another, all of one
width `W` (`LinearProgramming.vecStr`). Entry `i` is the block of the string from position `i * W`
(`LinearProgramming.blockOf`). Matrices are vectors in row-major order.

A vector is written in polynomial time when each entry is: the rule for the entries reads the
input `z` and the index `i`, written in unary, as complexitylib's loops over a range do, that is,
the string `pair z (1^i)` (`LinearProgramming.flatMap_range_mem_FP'`,
`LinearProgramming.vecStr_mem_FP`). Reading an entry at a polynomial-time index is
polynomial-time (`LinearProgramming.blockOf_mem_FP`).

## Main definitions

* `LinearProgramming.blockOf W x i`: the `i`-th block of width `W` of `x`, padded with `false`.
* `LinearProgramming.vecStr W f ℓ`: the words of `f 0, …, f (ℓ - 1)`.

## Main results

* `LinearProgramming.blockOf_vecStr`: reading back an entry.
* `LinearProgramming.flatMap_range_eq_vecStr`: a string built entry by entry is a vector.
* `LinearProgramming.blockOf_mem_FP`, `LinearProgramming.flatMap_range_mem_FP'`,
  `LinearProgramming.vecStr_mem_FP`, `LinearProgramming.WordFn.read`.
-/

namespace LinearProgramming

open Complexity

/-! ### Blocks -/

/-- Block `i` of width `W` of a string: the `W` digits from position `i * W`, padded with `false`
past the end of the string. -/
def blockOf (W : ℕ) (x : List Bool) (i : ℕ) : List Bool :=
  (x.drop (i * W) ++ List.replicate W false).take W

@[simp] theorem length_blockOf (W : ℕ) (x : List Bool) (i : ℕ) : (blockOf W x i).length = W := by
  simp only [blockOf, List.length_take, List.length_append, List.length_replicate]
  omega

theorem length_flatMap_range_const (ℓ W : ℕ) (g : ℕ → List Bool)
    (hg : ∀ i, (g i).length = W) : ((List.range ℓ).flatMap g).length = ℓ * W := by
  rw [List.length_flatMap]
  simp only [hg, List.map_const', List.sum_replicate, List.length_range, smul_eq_mul]

/-- Block `i` of a concatenation of blocks of width `W` is the `i`-th of them. -/
theorem blockOf_flatMap {W : ℕ} {g : ℕ → List Bool} (hg : ∀ i, (g i).length = W) :
    ∀ ℓ i, i < ℓ → blockOf W ((List.range ℓ).flatMap g) i = g i
  | 0, i, h => absurd h (Nat.not_lt_zero i)
  | ℓ + 1, i, h => by
    have hL : ((List.range ℓ).flatMap g).length = ℓ * W := length_flatMap_range_const ℓ W g hg
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    rcases Nat.lt_or_ge i ℓ with hi | hi
    · rw [← blockOf_flatMap hg ℓ i hi]
      unfold blockOf
      have hiW : (i + 1) * W ≤ ℓ * W := Nat.mul_le_mul_right _ hi
      rw [Nat.succ_mul] at hiW
      have hle : i * W ≤ ((List.range ℓ).flatMap g).length := by rw [hL]; omega
      have hW : W ≤ (List.drop (i * W) ((List.range ℓ).flatMap g)).length := by
        rw [List.length_drop, hL]
        omega
      rw [List.drop_append_of_le_length hle, List.append_assoc,
        List.take_append_of_le_length hW, List.take_append_of_le_length hW]
    · have hiℓ : i = ℓ := by omega
      subst hiℓ
      unfold blockOf
      rw [List.drop_left' (by rw [hL]), List.take_append_of_le_length (by rw [hg]),
        List.take_of_length_le (by rw [hg])]

theorem blockOf_mem_FP {W I : List Bool → ℕ} {X : List Bool → List Bool} (hW : UnaryFn W)
    (hX : X ∈ FP) (hI : UnaryFn I) : (fun z => blockOf (W z) (X z) (I z)) ∈ FP :=
  take_mem_FP (Cobham.appendFn_mem_FP (drop_mem_FP hX (hI.mul hW)) (hW.replicate_mem_FP false))
    hW

/-- A string cut or padded with `false` to length `W`. It is the identity on strings of length
`W`, and it makes the length of a computed block independent of its input. -/
def fitTo (W : ℕ) (s : List Bool) : List Bool := (s ++ List.replicate W false).take W

@[simp] theorem length_fitTo (W : ℕ) (s : List Bool) : (fitTo W s).length = W := by
  simp only [fitTo, List.length_take, List.length_append, List.length_replicate]
  omega

theorem fitTo_of_length {W : ℕ} {s : List Bool} (h : s.length = W) : fitTo W s = s := by
  rw [fitTo, List.take_append_of_le_length (by rw [h]), List.take_of_length_le (by rw [h])]

theorem fitTo_word (W : ℕ) (a : ℤ) : fitTo W (word W a) = word W a :=
  fitTo_of_length (length_word W a)

theorem fitTo_mem_FP {W : List Bool → ℕ} {X : List Bool → List Bool} (hW : UnaryFn W)
    (hX : X ∈ FP) : (fun z => fitTo (W z) (X z)) ∈ FP :=
  take_mem_FP (Cobham.appendFn_mem_FP hX (hW.replicate_mem_FP false)) hW

/-! ### Vectors -/

/-- The vector `f 0, …, f (ℓ - 1)`: the words of width `W` of its entries, one after another. -/
def vecStr (W : ℕ) (f : ℕ → ℤ) (ℓ : ℕ) : List Bool :=
  (List.range ℓ).flatMap fun i => word W (f i)

@[simp] theorem length_vecStr (W : ℕ) (f : ℕ → ℤ) (ℓ : ℕ) : (vecStr W f ℓ).length = ℓ * W :=
  length_flatMap_range_const ℓ W _ fun _ => length_word _ _

/-- **Reading an entry** of a vector. -/
theorem blockOf_vecStr {W : ℕ} {f : ℕ → ℤ} {ℓ i : ℕ} (hi : i < ℓ) :
    blockOf W (vecStr W f ℓ) i = word W (f i) :=
  blockOf_flatMap (fun _ => length_word _ _) ℓ i hi

/-- A string built entry by entry, each entry the word of the entry of `f`, is the vector of
`f`. -/
theorem flatMap_range_eq_vecStr {W : ℕ} {f : ℕ → ℤ} {ℓ : ℕ} {e : ℕ → List Bool}
    (he : ∀ i < ℓ, e i = word W (f i)) : (List.range ℓ).flatMap e = vecStr W f ℓ :=
  List.flatMap_congr fun i hi => he i (List.mem_range.mp hi)

theorem vecStr_congr {W ℓ : ℕ} {f g : ℕ → ℤ} (h : ∀ i < ℓ, f i = g i) :
    vecStr W f ℓ = vecStr W g ℓ :=
  flatMap_range_eq_vecStr fun i hi => by rw [h i hi]

/-- **Building a string entry by entry is polynomial-time.** The rule `e z i` is computed from
`pair z (1^i)`. -/
theorem flatMap_range_mem_FP' {ℓ : List Bool → ℕ} {e : List Bool → ℕ → List Bool}
    (hℓ : UnaryFn ℓ) (he : (fun y => e (pairFst y) (pairSnd y).length) ∈ FP) :
    (fun z => (List.range (ℓ z)).flatMap (e z)) ∈ FP :=
  mem_FP_of_eq (flatMap_range_mem_FP he hℓ) fun z => by
    simp only [List.length_replicate, pairFst_pair, pairSnd_pair]

/-- **Writing a vector entry by entry is polynomial-time.** -/
theorem vecStr_mem_FP {W ℓ : List Bool → ℕ} {f : List Bool → ℕ → ℤ} (hℓ : UnaryFn ℓ)
    (hf : WordFn (fun y => W (pairFst y)) fun y => f (pairFst y) (pairSnd y).length) :
    (fun z => vecStr (W z) (f z) (ℓ z)) ∈ FP :=
  flatMap_range_mem_FP' (e := fun z i => word (W z) (f z i)) hℓ hf

/-- **Reading an entry of a polynomial-time vector** at a polynomial-time index. -/
theorem WordFn.read {X : List Bool → List Bool} {W ℓ I : List Bool → ℕ} {f : List Bool → ℕ → ℤ}
    (hX : X ∈ FP) (hW : UnaryFn W) (hI : UnaryFn I)
    (hrep : ∀ z, X z = vecStr (W z) (f z) (ℓ z)) (hlt : ∀ z, I z < ℓ z) :
    WordFn W fun z => f z (I z) :=
  mem_FP_of_eq (blockOf_mem_FP hW hX hI) fun z => by rw [hrep z, blockOf_vecStr (hlt z)]

/-! ### Indexed contexts -/

/-- The context `pair z (1^i)` of a loop body: its input. -/
theorem ctx_mem_FP : (fun y : List Bool => pairFst y) ∈ FP := pairFst_mem_FP

/-- The context `pair z (1^i)` of a loop body: its index. -/
theorem UnaryFn.idx : UnaryFn fun y : List Bool => (pairSnd y).length := UnaryFn.index

/-- Reading through two nested loop contexts `pair (pair z (1^i)) (1^j)`: the input. -/
theorem ctx₂_mem_FP : (fun y : List Bool => pairFst (pairFst y)) ∈ FP :=
  mem_FP_comp pairFst_mem_FP pairFst_mem_FP

/-- Reading through two nested loop contexts `pair (pair z (1^i)) (1^j)`: the outer index. -/
theorem UnaryFn.idxOuter : UnaryFn fun y : List Bool => (pairSnd (pairFst y)).length :=
  UnaryFn.length (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)

end LinearProgramming
