import RSCounterexample.Paper.Complexity.Parse

/-!
# Unary inputs

The last sentence of Proposition 5.8 measures running time in `n + |a| + |b| + |c|`, the length
plus the sum of the entries: entries are counted in unary. Formally, the input is a triple of
lists of natural numbers whose entries are written in unary (`encodeTripleUnary`): the encoding
length is exactly `4 (|a| + |b| + |c|) + 2 (len a + len b + len c) + 8`
(`length_encodeTripleUnary`), so polynomial in the encoding length means polynomial in
`n + |a| + |b| + |c|`. The encoding is injective (`encodeTripleUnary_injective`).

## Main definitions

* `Schubert.RS.Algorithms.unaryList x`: `x` symbols `true`.
* `Schubert.RS.Algorithms.encodeTripleUnary a b c`: complexitylib's encoding of `[a, b, c]` with
  every entry written in unary.
-/

namespace Schubert.RS.Algorithms

open Complexity

/-- A natural number in unary: `x` symbols `true`. -/
def unaryList (x : ℕ) : List Bool := List.replicate x true

/-- **The unary encoding of `(a, b, c)`**: complexitylib's encoding of the list `[a, b, c]`, every
entry `x` written as the list of `x` symbols `true`. -/
def encodeTripleUnary (a b c : List ℕ) : List Bool :=
  DataEncode.bitstringEncode ([a, b, c].map fun l => l.map unaryList)

theorem unaryList_injective : Function.Injective unaryList := fun x y h => by
  simpa [unaryList] using congrArg List.length h

/-- The unary encoding is injective. -/
theorem encodeTripleUnary_injective {a b c a' b' c' : List ℕ}
    (h : encodeTripleUnary a b c = encodeTripleUnary a' b' c') : a = a' ∧ b = b' ∧ c = c' := by
  have h' := DataEncode.bitstringEncode_injective h
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h'
  have hinj : Function.Injective (List.map unaryList) := List.map_injective_iff.mpr
    unaryList_injective
  exact ⟨hinj h'.1, hinj h'.2.1, hinj h'.2.2⟩

theorem length_bitstringEncode_unaryList (x : ℕ) :
    (DataEncode.bitstringEncode (unaryList x)).length = 4 * x + 2 := by
  rw [length_bitstringEncode_list, unaryList]
  simp only [List.map_replicate, length_bitstringEncode_bool, ite_true, List.sum_replicate,
    smul_eq_mul]
  ring

theorem length_bitstringEncode_unary (l : List ℕ) :
    (DataEncode.bitstringEncode (l.map unaryList)).length = 4 * l.sum + 2 * l.length + 2 := by
  rw [length_bitstringEncode_list, List.map_map]
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Function.comp_apply,
      length_bitstringEncode_unaryList] at ih ⊢
    omega

/-- **The length of the unary encoding**: `4 (|a| + |b| + |c|) + 2 (len a + len b + len c) + 8`. -/
theorem length_encodeTripleUnary (a b c : List ℕ) :
    (encodeTripleUnary a b c).length =
      4 * (a.sum + b.sum + c.sum) + 2 * (a.length + b.length + c.length) + 8 := by
  rw [encodeTripleUnary, length_bitstringEncode_list]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    length_bitstringEncode_unary]
  ring

/-- For compositions of length `n`: the unary encoding has length
`4 (|a| + |b| + |c|) + 6 n + 8`, between `n + |a| + |b| + |c|` and six times it plus `8`. -/
theorem length_encodeTripleUnary_ofFn {n : ℕ} (a b c : Fin n → ℕ) :
    (encodeTripleUnary (List.ofFn a) (List.ofFn b) (List.ofFn c)).length =
      4 * (∑ i, a i + ∑ i, b i + ∑ i, c i) + 6 * n + 8 := by
  rw [length_encodeTripleUnary]
  simp only [List.sum_ofFn, List.length_ofFn]
  ring

/-! ### Reading the input -/

/-- The `ℓ`-th list of the triple, as a list of unary numerals. -/
theorem childStr_encodeTripleUnary (a b c : List ℕ) {ℓ : ℕ} (hℓ : ℓ < 3) :
    childStr ℓ (encodeTripleUnary a b c) =
      DataEncode.bitstringEncode ((listOf a b c ℓ).map unaryList) := by
  rw [encodeTripleUnary, childStr_bitstringEncode]
  rcases ℓ with _ | _ | _ | ℓ
  · rfl
  · rfl
  · rfl
  · omega

/-- Entry `i` of list `ℓ`, read from a unary encoding: the number of its symbols. -/
noncomputable def uent (ℓ i : ℕ) (z : List Bool) : ℕ := childNum (childStr i (childStr ℓ z))

/-- The length of list `ℓ`, read from a unary encoding. -/
noncomputable def ulen (ℓ : ℕ) (z : List Bool) : ℕ := childNum (childStr ℓ z)

theorem uent_unary {Z : List Bool → List Bool} {I : List Bool → ℕ} (hZ : Z ∈ FP)
    (hI : UnaryFn I) (ℓ : ℕ) : UnaryFn fun v => uent ℓ (I v) (Z v) :=
  childNum_unary (childStr_mem_FP hI (childStr_mem_FP (UnaryFn.const ℓ) hZ))

theorem ulen_unary {Z : List Bool → List Bool} (hZ : Z ∈ FP) (ℓ : ℕ) :
    UnaryFn fun v => ulen ℓ (Z v) :=
  childNum_unary (childStr_mem_FP (UnaryFn.const ℓ) hZ)

theorem uent_encodeTripleUnary (a b c : List ℕ) {ℓ : ℕ} (hℓ : ℓ < 3) {i : ℕ}
    (hi : i < (listOf a b c ℓ).length) :
    uent ℓ i (encodeTripleUnary a b c) = (listOf a b c ℓ)[i] := by
  rw [uent, childStr_encodeTripleUnary a b c hℓ, childStr_bitstringEncode, List.getElem?_map,
    List.getElem?_eq_getElem hi]
  simp only [Option.map_some, Option.getD_some]
  rw [unaryList, childNum_bitstringEncode, List.length_replicate]

theorem ulen_encodeTripleUnary (a b c : List ℕ) {ℓ : ℕ} (hℓ : ℓ < 3) :
    ulen ℓ (encodeTripleUnary a b c) = (listOf a b c ℓ).length := by
  rw [ulen, childStr_encodeTripleUnary a b c hℓ, childNum_bitstringEncode, List.length_map]

end Schubert.RS.Algorithms
