import Complexitylib.Classes.P
import Complexitylib.Classes.Containments.Internal.BinArith

/-!
# Fixed-width two's-complement words

A polynomial-time algorithm whose integers have polynomially bounded bit length can keep every
integer in a binary word of one fixed width `W`. The word of an integer `a` is the residue of `a`
modulo `2 ^ W`, written with `W` binary digits, least significant first (`LinearProgramming.word`).
Two integers that are congruent modulo `2 ^ W` have the same word (`LinearProgramming.word_congr`),
so ring operations on integers become ring operations on words. Reading an integer back from its
word, and tests such as `a < 0`, need `a` to fit: `|a| < 2 ^ (W - 1)`
(`LinearProgramming.Fits`).

## Main definitions

* `LinearProgramming.residue W a`: the residue of `a` modulo `2 ^ W`, as a natural number.
* `LinearProgramming.word W a`: the binary digits of the residue, `W` of them.
* `LinearProgramming.Fits W a`: `|a| < 2 ^ (W - 1)`.
* `LinearProgramming.msb x`: the last (most significant) digit of `x`, the sign of a word.
* `LinearProgramming.wordInt x`: the integer a word stands for, in two's complement.
* `LinearProgramming.WordFn W v`: the words of width `W z` of the integers `v z` can be written
  in polynomial time.

## Main results

* `LinearProgramming.eq_word_iff`: a string is the word of `a` exactly when it has length `W` and
  its value is congruent to `a` modulo `2 ^ W`.
* `LinearProgramming.msb_word`, `LinearProgramming.wordInt_word`: the sign and the value of a word
  of an integer that fits.
* `LinearProgramming.WordFn.ofNat`, `LinearProgramming.WordFn.ite`,
  `LinearProgramming.FPPred.neg_of_wordFn`: words of polynomial-time numbers, case distinctions
  and sign tests.
-/

namespace LinearProgramming

open Complexity

/-! ### Values of little-endian strings -/

theorem binValLE_eq_fromBitsLE : ∀ w : List Bool, binValLE w = Nat.fromBitsLE w
  | [] => by simp [binValLE, Nat.fromBitsLE, Nat.fromBits]
  | b :: w => by
    rw [binValLE_cons, Nat.fromBitsLE_cons, binValLE_eq_fromBitsLE w]
    cases b <;> simp

theorem binValLE_toBitsLE (W v : ℕ) : binValLE (Nat.toBitsLE W v) = v % 2 ^ W := by
  rw [binValLE_eq_fromBitsLE, Nat.fromBitsLE_toBitsLE_mod]

theorem toBitsLE_binValLE (x : List Bool) : Nat.toBitsLE x.length (binValLE x) = x := by
  rw [binValLE_eq_fromBitsLE, Nat.toBitsLE_fromBitsLE]

theorem toBitsLE_mod (W v : ℕ) : Nat.toBitsLE W (v % 2 ^ W) = Nat.toBitsLE W v :=
  Nat.fromBitsLE_inj_of_length_eq (by simp) (by
    rw [Nat.fromBitsLE_toBitsLE_mod, Nat.fromBitsLE_toBitsLE_mod, Nat.mod_mod])

/-- A string is the binary expansion of length `W` of a number below `2 ^ W` exactly when it has
length `W` and that value. -/
theorem eq_toBitsLE_iff {W v : ℕ} (hv : v < 2 ^ W) {x : List Bool} :
    x = Nat.toBitsLE W v ↔ x.length = W ∧ binValLE x = v := by
  constructor
  · rintro rfl
    exact ⟨Nat.length_toBitsLE W v, by rw [binValLE_toBitsLE, Nat.mod_eq_of_lt hv]⟩
  · rintro ⟨hlen, hval⟩
    rw [← hlen, ← hval, toBitsLE_binValLE]

/-! ### Words of integers -/

/-- The residue of `a` modulo `2 ^ W`, as a natural number. -/
def residue (W : ℕ) (a : ℤ) : ℕ := (a % 2 ^ W).toNat

theorem residue_cast (W : ℕ) (a : ℤ) : (residue W a : ℤ) = a % 2 ^ W :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))

theorem residue_lt (W : ℕ) (a : ℤ) : residue W a < 2 ^ W := by
  have h : (residue W a : ℤ) < 2 ^ W := by
    rw [residue_cast]
    exact Int.emod_lt_of_pos a (by positivity)
  exact_mod_cast h

theorem residue_congr {W : ℕ} {a b : ℤ} (h : a ≡ b [ZMOD 2 ^ W]) : residue W a = residue W b := by
  unfold residue
  rw [h]

theorem residue_natCast (W n : ℕ) : residue W n = n % 2 ^ W := by
  have h : (residue W n : ℤ) = ((n % 2 ^ W : ℕ) : ℤ) := by
    rw [residue_cast]
    push_cast
    rfl
  exact_mod_cast h

/-- The word of width `W` of an integer `a`: the `W` binary digits, least significant first, of the
residue of `a` modulo `2 ^ W`. -/
def word (W : ℕ) (a : ℤ) : List Bool := Nat.toBitsLE W (residue W a)

@[simp] theorem length_word (W : ℕ) (a : ℤ) : (word W a).length = W :=
  Nat.length_toBitsLE _ _

theorem binValLE_word (W : ℕ) (a : ℤ) : binValLE (word W a) = residue W a := by
  rw [word, binValLE_toBitsLE, Nat.mod_eq_of_lt (residue_lt W a)]

/-- Congruent integers have the same word. -/
theorem word_congr {W : ℕ} {a b : ℤ} (h : a ≡ b [ZMOD 2 ^ W]) : word W a = word W b := by
  rw [word, word, residue_congr h]

/-- A string is the word of `a` exactly when it has length `W` and its value is congruent to `a`
modulo `2 ^ W`. -/
theorem eq_word_iff {W : ℕ} {a : ℤ} {x : List Bool} :
    x = word W a ↔ x.length = W ∧ (binValLE x : ℤ) ≡ a [ZMOD 2 ^ W] := by
  constructor
  · rintro rfl
    refine ⟨length_word W a, ?_⟩
    rw [binValLE_word, residue_cast]
    exact Int.mod_modEq a _
  · rintro ⟨rfl, hval⟩
    have hlt : (binValLE x : ℤ) < 2 ^ x.length := by exact_mod_cast binValLE_lt x
    have heq : (binValLE x : ℤ) = residue x.length a := by
      rw [residue_cast, ← hval, Int.emod_eq_of_lt (by positivity) hlt]
    rw [word, ← Nat.cast_inj.mp heq, toBitsLE_binValLE]

theorem word_natCast (W n : ℕ) : word W n = Nat.toBitsLE W n := by
  rw [word, residue_natCast, toBitsLE_mod]

/-! ### Signs and values -/

/-- `a` fits into a word of width `W`: `|a| < 2 ^ (W - 1)`. -/
def Fits (W : ℕ) (a : ℤ) : Prop := |a| < 2 ^ (W - 1)

theorem Fits.mono {W W' : ℕ} {a : ℤ} (h : Fits W a) (hW : W ≤ W') : Fits W' a :=
  lt_of_lt_of_le h (pow_le_pow_right₀ (by norm_num) (by omega))

theorem fits_zero (W : ℕ) : Fits W 0 := by
  simp [Fits]

/-- The most significant digit of a string: its last digit, `false` for the empty string. For a
word of an integer that fits, it is the sign. -/
def msb (x : List Bool) : Bool := x[x.length - 1]?.getD false

theorem msb_toBitsLE_succ (w v : ℕ) (hv : v < 2 ^ (w + 1)) :
    msb (Nat.toBitsLE (w + 1) v) = decide (2 ^ w ≤ v) := by
  rw [msb, Nat.length_toBitsLE, toBitsLE_eq_map_range, Nat.add_sub_cancel,
    List.getElem?_map, List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.getD_some]
  have hdiv : v / 2 ^ w < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    rw [pow_succ] at hv
    omega
  by_cases h : 2 ^ w ≤ v
  · have h1 : v / 2 ^ w = 1 := by
      have : 1 ≤ v / 2 ^ w := (Nat.le_div_iff_mul_le (by positivity)).mpr (by omega)
      omega
    simp [h, h1]
  · have h0 : v / 2 ^ w = 0 := Nat.div_eq_of_lt (by omega)
    simp [h, h0]

/-- **The sign bit.** The most significant digit of the word of an integer that fits is its
sign. -/
theorem msb_word {W : ℕ} {a : ℤ} (h : Fits W a) : msb (word W a) = decide (a < 0) := by
  rcases W with _ | w
  · have ha : a = 0 := by
      have : |a| < 1 := by simpa [Fits] using h
      have := abs_lt.mp this
      omega
    subst ha
    rfl
  · rw [word, msb_toBitsLE_succ w _ (residue_lt _ _)]
    have hfit : |a| < 2 ^ w := by simpa [Fits] using h
    rw [abs_lt] at hfit
    have hres := residue_cast (w + 1) a
    have hpow : (2 : ℤ) ^ (w + 1) = 2 * 2 ^ w := by ring
    have h2w : (0 : ℤ) < 2 ^ w := by positivity
    by_cases ha : a < 0
    · have hmod : a % 2 ^ (w + 1) = a + 2 ^ (w + 1) := by
        rw [← Int.add_emod_right]
        exact Int.emod_eq_of_lt (by rw [hpow]; linarith) (by rw [hpow]; linarith)
      rw [hmod] at hres
      have : ((2 : ℕ) ^ w : ℤ) ≤ residue (w + 1) a := by
        rw [hres]
        push_cast
        rw [hpow]
        linarith
      simp only [ha, decide_true, decide_eq_true_eq]
      exact_mod_cast this
    · have hmod : a % 2 ^ (w + 1) = a := Int.emod_eq_of_lt (by linarith) (by rw [hpow]; linarith)
      rw [hmod] at hres
      have : (residue (w + 1) a : ℤ) < ((2 : ℕ) ^ w : ℤ) := by
        rw [hres]
        push_cast
        linarith
      simp only [ha, decide_false, decide_eq_false_iff_not, not_le]
      exact_mod_cast this

/-- The integer a word stands for in two's complement. -/
def wordInt (x : List Bool) : ℤ := if msb x then (binValLE x : ℤ) - 2 ^ x.length else binValLE x

/-- The word of an integer that fits stands for that integer. -/
theorem wordInt_word {W : ℕ} {a : ℤ} (h : Fits W a) : wordInt (word W a) = a := by
  rw [wordInt, msb_word h, length_word, binValLE_word, residue_cast]
  have hW : (2 : ℤ) ^ (W - 1) ≤ 2 ^ W := pow_le_pow_right₀ (by norm_num) (by omega)
  have hfit := h
  rw [Fits, abs_lt] at hfit
  by_cases ha : a < 0
  · rw [ite_eq_left (decide_eq_true ha)]
    have hmod : a % 2 ^ W = a + 2 ^ W := by
      rw [← Int.add_emod_right]
      exact Int.emod_eq_of_lt (by linarith) (by linarith)
    rw [hmod]
    ring
  · rw [ite_eq_right (by simpa using ha)]
    exact Int.emod_eq_of_lt (by linarith) (by linarith)

/-! ### Polynomial-time words -/

/-- The words of width `W z` of the integers `v z` can be written in polynomial time. -/
def WordFn (W : List Bool → ℕ) (v : List Bool → ℤ) : Prop :=
  (fun z => word (W z) (v z)) ∈ FP

variable {W : List Bool → ℕ} {v w : List Bool → ℤ}

theorem WordFn.mem_FP (hv : WordFn W v) : (fun z => word (W z) (v z)) ∈ FP := hv

theorem WordFn.of_eq (hv : WordFn W v) (h : ∀ z, v z = w z) : WordFn W w :=
  mem_FP_of_eq hv fun z => by rw [h z]

/-- Only the residues modulo `2 ^ W` matter. -/
theorem WordFn.of_modEq (hv : WordFn W v) (h : ∀ z, v z ≡ w z [ZMOD 2 ^ W z]) : WordFn W w :=
  mem_FP_of_eq hv fun z => word_congr (h z)

theorem WordFn.comp (hv : WordFn W v) {h : List Bool → List Bool} (hh : h ∈ FP) :
    WordFn (fun z => W (h z)) (fun z => v (h z)) := by
  have h' := mem_FP_comp hh hv
  exact h'

/-- The width of polynomial-time words is a polynomial-time number. -/
theorem WordFn.width (hv : WordFn W v) : UnaryFn W :=
  (UnaryFn.length hv).of_eq fun _ => length_word _ _

/-- Words of polynomial-time numbers. -/
theorem WordFn.ofNat (hW : UnaryFn W) {n : List Bool → ℕ} (hn : UnaryFn n) :
    WordFn W fun z => (n z : ℤ) :=
  mem_FP_of_eq (toBitsLE_mem_FP hW hn) fun _ => (word_natCast _ _).symm

theorem WordFn.zero (hW : UnaryFn W) : WordFn W fun _ => 0 :=
  (WordFn.ofNat hW (UnaryFn.const 0)).of_eq fun _ => Nat.cast_zero

/-- Case distinction on a polynomial-time test. -/
theorem WordFn.ite {p : List Bool → Prop} [DecidablePred p] (hp : FPPred p) (hv : WordFn W v)
    (hw : WordFn W w) : WordFn W fun z => if p z then v z else w z :=
  mem_FP_of_eq (FPPred.ite_mem_FP hp hv hw) fun z => by
    by_cases h : p z
    · simp only [h, ite_true]
    · simp only [h, ite_false]

theorem msb_mem_FP {X : List Bool → List Bool} (hX : X ∈ FP) : (fun z => [msb (X z)]) ∈ FP :=
  getBit_mem_FP hX ((UnaryFn.length hX).sub (UnaryFn.const 1))

/-- **Sign tests** of integers that fit their words are polynomial-time. -/
theorem FPPred.neg_of_wordFn (hv : WordFn W v) (hfit : ∀ z, Fits (W z) (v z)) :
    FPPred fun z => v z < 0 :=
  FPPred.of_iff (FPPred.of_flag (msb_mem_FP hv)) fun z => by
    rw [msb_word (hfit z), decide_eq_true_iff]

end LinearProgramming
