import Schubert.RS.Quiver.Triple.Canonical
import Complexitylib.Encoding.DataEncode
import Mathlib.Data.Nat.Size

/-!
# Inputs of the quiver algorithms

The algorithms of Theorem 1.4 take a triple `(a, b, c)` of weak compositions of the same length
`n`, with entries in binary. Formally, the input is a triple of lists of natural numbers, encoded
as a bitstring by complexitylib's canonical encoding (`encodeTriple`). The length `n` is part of
the input, and the encoding length is linear in the total binary length (`binarySize`).

## Main definitions

* `encodeTriple a b c`: the bitstring encoding of the list `[a, b, c]`.
* `toComposition n x`: the list `x` as a weak composition of length `n` (padded with zeros).
* `IsQuiverTripleList a b c`: the three lists have the same length and form a quiver triple
  (Definition 5.1).
* `atomCoefficientList a b c`: the coefficient of `𝒜_c` in `κ_a κ_b`.

## Main results

* `binarySize_le_length`, `length_le_binarySize`: the encoding length is linear in the binary
  size.
-/

namespace Schubert.RS.Algorithms

open Quiver

noncomputable section

/-- The bitstring encoding of an input triple `(a, b, c)`: complexitylib's canonical encoding of
the list `[a, b, c]`, natural numbers in binary. -/
def encodeTriple (a b c : List ℕ) : List Bool :=
  Complexity.DataEncode.bitstringEncode [a, b, c]

/-- The total binary length `∑ (bit length + 1)` of the entries of `a`, `b`, `c`. -/
def binarySize (a b c : List ℕ) : ℕ :=
  ((a ++ b ++ c).map fun x => Nat.size x + 1).sum

/-- A list as a weak composition of length `n`: entries beyond the list are `0`. -/
def toComposition (n : ℕ) (x : List ℕ) : Composition n := fun i => x.getD i 0

/-- The lists `a`, `b`, `c` have the same length and form a quiver triple. -/
def IsQuiverTripleList (a b c : List ℕ) : Prop :=
  a.length = c.length ∧ b.length = c.length ∧
    IsQuiverTriple (toComposition c.length a) (toComposition c.length b)
      (toComposition c.length c)

instance (a b c : List ℕ) : Decidable (IsQuiverTripleList a b c) := by
  unfold IsQuiverTripleList
  infer_instance

/-- The answer of the recognition problem. -/
def isQuiverTripleListBool (a b c : List ℕ) : Bool := decide (IsQuiverTripleList a b c)

theorem isQuiverTripleListBool_iff (a b c : List ℕ) :
    isQuiverTripleListBool a b c = true ↔ IsQuiverTripleList a b c :=
  decide_eq_true_iff

/-- The coefficient of `𝒜_c` in `κ_a κ_b`, for lists of the same length. -/
def atomCoefficientList (a b c : List ℕ) : ℤ :=
  atomCoefficient (key (toComposition c.length a) * key (toComposition c.length b))
    (toComposition c.length c)

/-! ### Encoding lengths -/

open Complexity

theorem length_bitstringEncode_list {α : Type} [DataEncode α] (l : List α) :
    (DataEncode.bitstringEncode l).length =
      ((l.map fun x => (DataEncode.bitstringEncode x).length).sum) + 2 := by
  rw [DataEncode.bitstringEncode_list]
  simp only [List.length_cons, List.length_append, List.length_flatten, List.map_map]
  rfl

theorem length_bitstringEncode_bool (x : Bool) :
    (DataEncode.bitstringEncode x).length = if x then 4 else 2 := by
  cases x <;> simp [DataEncode.bitstringEncode, DataEncode.encode, Data.toBits_l]

theorem length_bitstringEncode_nat (x : ℕ) :
    (DataEncode.bitstringEncode x).length =
      ((x.bits.map fun b => if b then 4 else 2).sum) + 2 := by
  change (DataEncode.bitstringEncode x.bits).length = _
  rw [length_bitstringEncode_list]
  simp only [length_bitstringEncode_bool]

theorem size_mul_two_le (x : ℕ) :
    2 * Nat.size x + 2 ≤ (DataEncode.bitstringEncode x).length := by
  rw [length_bitstringEncode_nat, ← Nat.size_eq_bits_len]
  suffices h : ∀ l : List Bool, 2 * l.length ≤ (l.map fun b => if b then 4 else 2).sum by
    have := h x.bits
    omega
  intro l
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    split_ifs <;> omega

theorem length_le_size_mul_four (x : ℕ) :
    (DataEncode.bitstringEncode x).length ≤ 4 * Nat.size x + 2 := by
  rw [length_bitstringEncode_nat, ← Nat.size_eq_bits_len]
  suffices h : ∀ l : List Bool, (l.map fun b => if b then 4 else 2).sum ≤ 4 * l.length by
    have := h x.bits
    omega
  intro l
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    split_ifs <;> omega

theorem length_encodeTriple (a b c : List ℕ) :
    (encodeTriple a b c).length =
      ((a ++ b ++ c).map fun x => (DataEncode.bitstringEncode x).length).sum + 8 := by
  rw [encodeTriple, length_bitstringEncode_list]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    length_bitstringEncode_list, List.map_append, List.sum_append]
  omega

/-- The encoding is at least as long as the binary size. -/
theorem binarySize_le_length (a b c : List ℕ) : binarySize a b c ≤ (encodeTriple a b c).length := by
  rw [length_encodeTriple, binarySize]
  suffices h : ∀ l : List ℕ, (l.map fun x => Nat.size x + 1).sum ≤
      (l.map fun x => (DataEncode.bitstringEncode x).length).sum by
    have := h (a ++ b ++ c)
    omega
  intro l
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := size_mul_two_le x
    omega

/-- The encoding length is linear in the binary size. -/
theorem length_le_binarySize (a b c : List ℕ) :
    (encodeTriple a b c).length ≤ 4 * binarySize a b c + 8 := by
  rw [length_encodeTriple, binarySize]
  suffices h : ∀ l : List ℕ, (l.map fun x => (DataEncode.bitstringEncode x).length).sum ≤
      4 * (l.map fun x => Nat.size x + 1).sum by
    have := h (a ++ b ++ c)
    omega
  intro l
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := length_le_size_mul_four x
    omega

end

end Schubert.RS.Algorithms
