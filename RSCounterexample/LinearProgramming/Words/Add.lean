import RSCounterexample.LinearProgramming.Words.Basic

/-!
# Addition, negation and comparison of words

Words of equal width are added with complexitylib's binary adder `Complexity.addBits`, dropping
the carry out, so the sum is taken modulo `2 ^ W` (`LinearProgramming.wadd_word`). Negation is the
complement plus one (`LinearProgramming.wneg_word`). These are ring operations on residues, so
they need no assumption on the size of the integers. Comparisons are sign tests of differences,
and these do need the difference to fit its word.

## Main definitions

* `LinearProgramming.wadd`, `LinearProgramming.wnot`, `LinearProgramming.wneg`,
  `LinearProgramming.wsub`: sum, complement, negation and difference of words.

## Main results

* `LinearProgramming.wadd_word`, `LinearProgramming.wneg_word`, `LinearProgramming.wsub_word`: the
  operations on words of integers.
* `LinearProgramming.WordFn.add`, `LinearProgramming.WordFn.neg`, `LinearProgramming.WordFn.sub`,
  `LinearProgramming.WordFn.const`: closure of polynomial-time words.
* `LinearProgramming.FPPred.lt_of_wordFn`, `LinearProgramming.FPPred.le_of_wordFn`,
  `LinearProgramming.FPPred.eq_of_wordFn`: comparisons of integers whose difference fits.
-/

namespace LinearProgramming

open Complexity

/-- `(residue W a : ℤ)` is congruent to `a` modulo `2 ^ W`. -/
theorem residue_modEq (W : ℕ) (a : ℤ) : (residue W a : ℤ) ≡ a [ZMOD 2 ^ W] := by
  rw [residue_cast]
  exact Int.mod_modEq a _

/-! ### Addition -/

/-- The sum of two words of equal width, modulo `2 ^ width`: the carry out is dropped. -/
def wadd (x y : List Bool) : List Bool := addBits x y

theorem length_wadd (x y : List Bool) (h : y.length = x.length) :
    (wadd x y).length = x.length :=
  addBits_length x y h

/-- The adder computes the sum modulo `2 ^ width`. -/
theorem binValLE_wadd (x y : List Bool) (h : y.length = x.length) :
    binValLE (wadd x y) = (binValLE x + binValLE y) % 2 ^ x.length := by
  have hk := addBitsLE_binValLE false x y h
  have hlt := binValLE_lt (addBitsLE false x y).2
  rw [addBitsLE_length] at hlt
  rw [wadd, addBits_eq x y h]
  simp only [Bool.toNat_false, Nat.add_zero] at hk
  rw [← hk]
  cases (addBitsLE false x y).1
  · simp only [Bool.toNat_false, Nat.zero_mul, Nat.add_zero]
    exact (Nat.mod_eq_of_lt hlt).symm
  · simp only [Bool.toNat_true, Nat.one_mul, Nat.add_mod_right]
    exact (Nat.mod_eq_of_lt hlt).symm

/-- **Addition of words.** -/
theorem wadd_word (W : ℕ) (a b : ℤ) : wadd (word W a) (word W b) = word W (a + b) := by
  rw [eq_word_iff]
  refine ⟨by rw [length_wadd _ _ (by simp), length_word], ?_⟩
  rw [binValLE_wadd _ _ (by simp), length_word, binValLE_word, binValLE_word]
  push_cast
  exact (Int.mod_modEq _ _).trans ((residue_modEq W a).add (residue_modEq W b))

theorem wadd_mem_FP {X Y : List Bool → List Bool} (hX : X ∈ FP) (hY : Y ∈ FP) :
    (fun z => wadd (X z) (Y z)) ∈ FP :=
  addBitsFn_mem_FP hX hY

variable {W : List Bool → ℕ} {v w : List Bool → ℤ}

theorem WordFn.add (hv : WordFn W v) (hw : WordFn W w) : WordFn W fun z => v z + w z :=
  mem_FP_of_eq (wadd_mem_FP hv hw) fun _ => wadd_word _ _ _

/-! ### Negation and subtraction -/

/-- The complement of a word: every digit flipped. -/
def wnot (x : List Bool) : List Bool := x.map not

@[simp] theorem length_wnot (x : List Bool) : (wnot x).length = x.length := by
  simp [wnot]

theorem binValLE_wnot : ∀ x : List Bool, binValLE (wnot x) + binValLE x + 1 = 2 ^ x.length
  | [] => by simp [wnot, binValLE]
  | b :: x => by
    have ih := binValLE_wnot x
    simp only [wnot, List.map_cons] at ih ⊢
    rw [binValLE_cons, binValLE_cons, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

theorem wnot_mem_FP {X : List Bool → List Bool} (hX : X ∈ FP) : (fun z => wnot (X z)) ∈ FP := by
  have hG : (fun y => notBit [(X (pairFst y))[(pairSnd y).length]?.getD false]) ∈ FP :=
    notBitFn_mem_FP (getBit_mem_FP (mem_FP_comp pairFst_mem_FP hX) UnaryFn.index)
  refine mem_FP_of_eq (bitwise_mem_FP (len := fun z => (X z).length)
    (b := fun z t => !(X z)[t]?.getD false) (UnaryFn.length hX) hG fun z i => by
      simp [notBit_singleton]) fun z => ?_
  apply List.ext_getElem
  · simp [wnot]
  · intro i h1 h2
    have hi : i < (X z).length := by simpa [wnot] using h2
    simp [wnot, List.getElem?_eq_getElem hi]

/-- The negation of a word: its complement plus one. -/
def wneg (x : List Bool) : List Bool := wadd (wnot x) (Nat.toBitsLE x.length 1)

/-- **Negation of words.** -/
theorem wneg_word (W : ℕ) (a : ℤ) : wneg (word W a) = word W (-a) := by
  have hc := binValLE_wnot (word W a)
  rw [length_word, binValLE_word] at hc
  rw [eq_word_iff, wneg]
  refine ⟨by rw [length_wadd _ _ (by simp), length_wnot, length_word], ?_⟩
  rw [binValLE_wadd _ _ (by simp), length_wnot, length_word, binValLE_toBitsLE]
  have hcz : (binValLE (wnot (word W a)) : ℤ) = 2 ^ W - 1 - residue W a := by
    have : ((binValLE (wnot (word W a)) + residue W a + 1 : ℕ) : ℤ) = ((2 ^ W : ℕ) : ℤ) := by
      rw [hc]
    push_cast at this
    linarith
  push_cast
  rw [hcz]
  refine (Int.mod_modEq _ _).trans ?_
  refine (Int.ModEq.add_left _ (Int.mod_modEq 1 _)).trans ?_
  have hr := residue_modEq W a
  rw [Int.modEq_iff_dvd] at hr ⊢
  obtain ⟨k, hk⟩ := hr
  exact ⟨-k - 1, by linarith⟩

theorem length_wneg (x : List Bool) : (wneg x).length = x.length := by
  rw [wneg, length_wadd _ _ (by simp), length_wnot]

theorem wneg_mem_FP {X : List Bool → List Bool} (hX : X ∈ FP) : (fun z => wneg (X z)) ∈ FP :=
  wadd_mem_FP (wnot_mem_FP hX) (toBitsLE_mem_FP (UnaryFn.length hX) (UnaryFn.const 1))

theorem WordFn.neg (hv : WordFn W v) : WordFn W fun z => -v z :=
  mem_FP_of_eq (wneg_mem_FP hv) fun _ => wneg_word _ _

/-- The difference of two words. -/
def wsub (x y : List Bool) : List Bool := wadd x (wneg y)

/-- **Subtraction of words.** -/
theorem wsub_word (W : ℕ) (a b : ℤ) : wsub (word W a) (word W b) = word W (a - b) := by
  rw [wsub, wneg_word, wadd_word, sub_eq_add_neg]

theorem wsub_mem_FP {X Y : List Bool → List Bool} (hX : X ∈ FP) (hY : Y ∈ FP) :
    (fun z => wsub (X z) (Y z)) ∈ FP :=
  wadd_mem_FP hX (wneg_mem_FP hY)

theorem WordFn.sub (hv : WordFn W v) (hw : WordFn W w) : WordFn W fun z => v z - w z :=
  mem_FP_of_eq (wsub_mem_FP hv hw) fun _ => wsub_word _ _ _

/-- Words of a constant integer. -/
theorem WordFn.const (hW : UnaryFn W) (c : ℤ) : WordFn W fun _ => c :=
  ((WordFn.ofNat hW (UnaryFn.const c.toNat)).sub (WordFn.ofNat hW (UnaryFn.const (-c).toNat))).of_eq
    fun _ => Int.toNat_sub_toNat_neg c

/-! ### Comparisons -/

theorem fits_neg_iff {W : ℕ} {a : ℤ} : Fits W (-a) ↔ Fits W a := by
  simp [Fits]

/-- **Comparison** of integers whose difference fits its word. -/
theorem FPPred.lt_of_wordFn (hv : WordFn W v) (hw : WordFn W w)
    (hfit : ∀ z, Fits (W z) (v z - w z)) : FPPred fun z => v z < w z :=
  (FPPred.neg_of_wordFn (hv.sub hw) hfit).of_iff fun _ => sub_neg

theorem FPPred.le_of_wordFn (hv : WordFn W v) (hw : WordFn W w)
    (hfit : ∀ z, Fits (W z) (v z - w z)) : FPPred fun z => v z ≤ w z := by
  have hfit' : ∀ z, Fits (W z) (w z - v z) := fun z => by
    rw [← neg_sub]
    exact fits_neg_iff.mpr (hfit z)
  exact (FPPred.lt_of_wordFn hw hv hfit').not.of_iff fun _ => not_lt

theorem FPPred.eq_of_wordFn (hv : WordFn W v) (hw : WordFn W w)
    (hfit : ∀ z, Fits (W z) (v z - w z)) : FPPred fun z => v z = w z := by
  have hfit' : ∀ z, Fits (W z) (w z - v z) := fun z => by
    rw [← neg_sub]
    exact fits_neg_iff.mpr (hfit z)
  exact ((FPPred.le_of_wordFn hv hw hfit).and (FPPred.le_of_wordFn hw hv hfit')).of_iff
    fun _ => le_antisymm_iff.symm

/-- Positivity of an integer that fits its word. -/
theorem FPPred.pos_of_wordFn (hv : WordFn W v) (hfit : ∀ z, Fits (W z) (v z)) :
    FPPred fun z => 0 < v z :=
  (FPPred.neg_of_wordFn hv.neg fun z => fits_neg_iff.mpr (hfit z)).of_iff fun _ => neg_neg_iff_pos

end LinearProgramming
