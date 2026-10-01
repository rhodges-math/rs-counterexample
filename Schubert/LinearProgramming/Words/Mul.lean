import Schubert.LinearProgramming.Words.Add

/-!
# Multiplication of words

Words are multiplied by the schoolbook method: read the digits of the multiplier from the most
significant one down, doubling the accumulated product and adding the multiplicand at every digit
`1`. Doubling is a shift by one place inside the width, so the product is taken modulo `2 ^ W`
(`LinearProgramming.wmul_word`). It is a ring operation on residues and needs no assumption on the
size of the integers. The loop is a fold over the digits of the multiplier with states of the
fixed width, so it is polynomial-time (`LinearProgramming.wmul_mem_FP`).

Shifting a word up by `k` places multiplies by `2 ^ k` (`LinearProgramming.wshl_word`).

## Main definitions

* `LinearProgramming.shiftUp`: doubling inside the width.
* `LinearProgramming.wmul`: the product of two words of equal width.
* `LinearProgramming.wshl`: the shift up by `k` places.

## Main results

* `LinearProgramming.binValLE_take`: truncation is reduction modulo a power of two.
* `LinearProgramming.wmul_word`, `LinearProgramming.wmul_mem_FP`, `LinearProgramming.WordFn.mul`.
* `LinearProgramming.wshl_word`, `LinearProgramming.wshl_mem_FP`,
  `LinearProgramming.WordFn.mul_pow`.
-/

namespace LinearProgramming

open Complexity

/-- Truncating a string to its first `k` digits reduces its value modulo `2 ^ k`. -/
theorem binValLE_take : ∀ (k : ℕ) (x : List Bool), binValLE (x.take k) = binValLE x % 2 ^ k
  | 0, x => by simp [binValLE, Nat.mod_one]
  | k + 1, [] => by simp [binValLE]
  | k + 1, b :: x => by
    rw [List.take_succ_cons, binValLE_cons, binValLE_cons, binValLE_take k x, pow_succ]
    have hb : b.toNat < 2 := by cases b <;> simp
    have hm : 0 < 2 ^ k := by positivity
    have hd := Nat.div_add_mod (binValLE x) (2 ^ k)
    have hr := Nat.mod_lt (binValLE x) hm
    set q := binValLE x / 2 ^ k
    set r := binValLE x % 2 ^ k
    have he : b.toNat + 2 * binValLE x = (b.toNat + 2 * r) + 2 ^ k * 2 * q := by
      rw [← hd]
      ring
    rw [he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-! ### Doubling -/

/-- Doubling inside the width: the shift up by one place, dropping the top digit. -/
def shiftUp (r : List Bool) : List Bool := (false :: r).take r.length

@[simp] theorem length_shiftUp (r : List Bool) : (shiftUp r).length = r.length := by
  simp [shiftUp]

theorem binValLE_shiftUp (r : List Bool) :
    binValLE (shiftUp r) = 2 * binValLE r % 2 ^ r.length := by
  rw [shiftUp, binValLE_take, binValLE_cons]
  simp

theorem shiftUp_mem_FP {X : List Bool → List Bool} (hX : X ∈ FP) :
    (fun z => shiftUp (X z)) ∈ FP :=
  take_mem_FP (mem_FP_comp hX (Cobham.cons_mem_FP false)) (UnaryFn.length hX)

/-! ### Multiplication -/

/-- The product of `x` with the multiplier `t`, accumulated over the digits of `t` from the most
significant one down, modulo `2 ^ |x|`. -/
def mulAux (x : List Bool) : List Bool → List Bool
  | [] => List.replicate x.length false
  | false :: t => shiftUp (mulAux x t)
  | true :: t => wadd (shiftUp (mulAux x t)) x

theorem length_mulAux (x : List Bool) : ∀ t, (mulAux x t).length = x.length
  | [] => by simp [mulAux]
  | false :: t => by rw [mulAux, length_shiftUp, length_mulAux x t]
  | true :: t => by
    rw [mulAux, length_wadd _ _ (by rw [length_shiftUp, length_mulAux x t]), length_shiftUp,
      length_mulAux x t]

theorem binValLE_mulAux (x : List Bool) :
    ∀ t, binValLE (mulAux x t) = binValLE x * binValLE t % 2 ^ x.length
  | [] => by simp [mulAux, binValLE_replicate_false, binValLE]
  | false :: t => by
    rw [mulAux, binValLE_shiftUp, length_mulAux, binValLE_mulAux x t, binValLE_cons,
      Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
    simp only [Bool.toNat_false, Nat.zero_add]
    ring_nf
  | true :: t => by
    rw [mulAux, binValLE_wadd _ _ (by rw [length_shiftUp, length_mulAux]), length_shiftUp,
      length_mulAux, binValLE_shiftUp, length_mulAux, binValLE_mulAux x t, binValLE_cons,
      Nat.mul_mod 2, Nat.mod_mod, ← Nat.mul_mod, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    simp only [Bool.toNat_true]
    ring_nf

/-- The product of two words of equal width, modulo `2 ^ width`. -/
def wmul (x y : List Bool) : List Bool := mulAux x y

theorem length_wmul (x y : List Bool) : (wmul x y).length = x.length :=
  length_mulAux x y

/-- **Multiplication of words.** -/
theorem wmul_word (W : ℕ) (a b : ℤ) : wmul (word W a) (word W b) = word W (a * b) := by
  rw [eq_word_iff]
  refine ⟨by rw [length_wmul, length_word], ?_⟩
  rw [wmul, binValLE_mulAux, length_word, binValLE_word, binValLE_word]
  push_cast
  exact (Int.mod_modEq _ _).trans ((residue_modEq W a).mul (residue_modEq W b))

theorem wmul_mem_FP {X Y : List Bool → List Bool} (hX : X ∈ FP) (hY : Y ∈ FP) :
    (fun z => wmul (X z) (Y z)) ∈ FP := by
  have hacc : (fun q => shiftUp (pairSnd (pairFst q))) ∈ FP :=
    shiftUp_mem_FP (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
  have hB : (fun q => wadd (shiftUp (pairSnd (pairFst q))) (pairFst (pairFst q))) ∈ FP :=
    wadd_mem_FP hacc (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  obtain ⟨p, hp⟩ := Cobham.output_length_poly_of_mem_FP hX
  exact recFold_mem_FP_of_bound (g := fun z t => mulAux (X z) t) hacc hB
    ((UnaryFn.length hX).replicate_mem_FP false) hX hY (fun _ => rfl)
    (fun _ _ => by simp [mulAux]) (fun _ _ => by simp [mulAux]) (PolyBound.eval p)
    fun z t _ => by rw [length_mulAux]; exact hp z

variable {W : List Bool → ℕ} {v w : List Bool → ℤ}

theorem WordFn.mul (hv : WordFn W v) (hw : WordFn W w) : WordFn W fun z => v z * w z :=
  mem_FP_of_eq (wmul_mem_FP hv hw) fun _ => wmul_word _ _ _

/-! ### Shifts -/

/-- The shift of a word up by `k` places, inside its width. -/
def wshl (x : List Bool) (k : ℕ) : List Bool := (List.replicate k false ++ x).take x.length

theorem length_wshl (x : List Bool) (k : ℕ) : (wshl x k).length = x.length := by
  simp [wshl]

/-- **Shifting multiplies by a power of two.** -/
theorem wshl_word (W : ℕ) (a : ℤ) (k : ℕ) : wshl (word W a) k = word W (a * 2 ^ k) := by
  rw [eq_word_iff]
  refine ⟨by rw [length_wshl, length_word], ?_⟩
  rw [wshl, binValLE_take, binValLE_replicate_false_append, length_word, binValLE_word]
  push_cast
  refine (Int.mod_modEq _ _).trans ?_
  rw [mul_comm]
  exact (residue_modEq W a).mul_right _

theorem wshl_mem_FP {X : List Bool → List Bool} (hX : X ∈ FP) {K : List Bool → ℕ}
    (hK : UnaryFn K) : (fun z => wshl (X z) (K z)) ∈ FP :=
  take_mem_FP (Cobham.appendFn_mem_FP (hK.replicate_mem_FP false) hX) (UnaryFn.length hX)

theorem WordFn.mul_pow (hv : WordFn W v) {K : List Bool → ℕ} (hK : UnaryFn K) :
    WordFn W fun z => v z * 2 ^ K z :=
  mem_FP_of_eq (wshl_mem_FP hv hK) fun _ => wshl_word _ _ _

end LinearProgramming
