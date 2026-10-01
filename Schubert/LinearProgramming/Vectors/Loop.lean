import Schubert.LinearProgramming.Vectors.Blocks

/-!
# Loops with states of fixed length

A loop runs `K` rounds, and round `i` maps the state `s` to `step i s`
(`LinearProgramming.loopN`). On strings it is polynomial-time when the round is polynomial-time
(as a function of the input, the round number in unary and the state), the number of rounds is a
polynomial-time number, and every round keeps the state at one polynomial-time length
(`LinearProgramming.loopN_mem_FP`). This needs no information about what the states mean.

What the states mean is a separate induction (`LinearProgramming.loopN_semiconj`): if the string
round maps the encoding of every state along the run of a loop on some other type to the encoding
of the next state, then the string loop computes the encoding of the final state.

Sums of words over a range are loops (`LinearProgramming.sumWords_mem_FP`,
`LinearProgramming.WordFn.sum`).

## Main definitions

* `LinearProgramming.loopN`: `K` rounds of a loop.
* `LinearProgramming.sumWords`: the sum of `n` words.

## Main results

* `LinearProgramming.loopN_mem_FP`: loops with fixed-length states are polynomial-time.
* `LinearProgramming.loopN_semiconj`: a loop on strings computes a loop on encoded values.
* `LinearProgramming.WordFn.sum`: sums over a polynomial-time range.
-/

namespace LinearProgramming

open Complexity

/-- `K` rounds of a loop: round `i` maps the state `s` to `step i s`. -/
def loopN {α : Type*} (step : ℕ → α → α) : ℕ → α → α
  | 0, s => s
  | k + 1, s => step k (loopN step k s)

@[simp] theorem loopN_zero {α : Type*} (step : ℕ → α → α) (s : α) : loopN step 0 s = s := rfl

theorem loopN_succ {α : Type*} (step : ℕ → α → α) (k : ℕ) (s : α) :
    loopN step (k + 1) s = step k (loopN step k s) := rfl

/-- **A loop computes a loop on encoded values**, as long as every round along the run maps
encodings to encodings. -/
theorem loopN_semiconj {α β : Type*} (enc : α → β) (step : ℕ → β → β) (T : ℕ → α → α) (s : α)
    (K : ℕ) (h : ∀ i < K, step i (enc (loopN T i s)) = enc (T i (loopN T i s))) :
    loopN step K (enc s) = enc (loopN T K s) := by
  induction K with
  | zero => rfl
  | succ K ih =>
    rw [loopN_succ, loopN_succ, ih fun i hi => h i (by omega), h K (by omega)]

/-- An invariant that every round preserves holds along the whole run. -/
theorem loopN_induction {α : Type*} (step : ℕ → α → α) (P : α → Prop) (s : α) (K : ℕ)
    (h0 : P s) (h : ∀ i < K, ∀ t, P t → P (step i t)) : P (loopN step K s) := by
  induction K with
  | zero => exact h0
  | succ K ih => exact h K (by omega) _ (ih fun i hi => h i (by omega))

theorem length_loopN {step : ℕ → List Bool → List Bool} {ℓ : ℕ}
    (hlen : ∀ i s, s.length = ℓ → (step i s).length = ℓ) {s : List Bool} (hs : s.length = ℓ)
    (K : ℕ) : (loopN step K s).length = ℓ :=
  loopN_induction step (fun t => t.length = ℓ) s K hs fun i _ t ht => hlen i t ht

/-- **Loops with states of fixed length are polynomial-time.** The round `step z i s` must be
polynomial-time as a function of `pair (pair z s) (1^i)`, keep the length `ℓ z` of the state,
and the start and the number of rounds must be polynomial-time. -/
theorem loopN_mem_FP {step : List Bool → ℕ → List Bool → List Bool}
    {init : List Bool → List Bool} {K ℓ : List Bool → ℕ}
    (hstep : (fun q => step (pairFst (pairFst q)) (pairSnd q).length (pairSnd (pairFst q))) ∈ FP)
    (hinit : init ∈ FP) (hK : UnaryFn K) (hℓ : UnaryFn ℓ)
    (hlen : ∀ z i s, s.length = ℓ z → (step z i s).length = ℓ z)
    (hinit_len : ∀ z, (init z).length = ℓ z) :
    (fun z => loopN (step z) (K z) (init z)) ∈ FP := by
  obtain ⟨p, hp⟩ := Cobham.output_length_poly_of_mem_FP hℓ
  have hg : ∀ z (t : List Bool), (loopN (step z) t.length (init z)).length = ℓ z :=
    fun z t => length_loopN (hlen z) (hinit_len z) _
  refine mem_FP_of_eq (recFold_mem_FP_of_bound (g := fun z t => loopN (step z) t.length (init z))
    hstep hstep hinit id_mem_FP hK (fun _ => rfl) (fun z t => ?_) (fun z t => ?_)
    (PolyBound.eval p) fun z t _ => ?_) fun z => ?_
  · simp [loopN_succ]
  · simp [loopN_succ]
  · rw [hg]
    simpa using hp z
  · simp

/-! ### Sums -/

/-- The sum of the words `e 0, …, e (n - 1)` of width `W`. -/
def sumWords (W : ℕ) (e : ℕ → List Bool) (n : ℕ) : List Bool :=
  loopN (fun i acc => wadd acc (e i)) n (List.replicate W false)

/-- **The sum of words** is the word of the sum. -/
theorem sumWords_eq {W n : ℕ} {e : ℕ → List Bool} {f : ℕ → ℤ}
    (he : ∀ i < n, e i = word W (f i)) : sumWords W e n = word W (∑ i ∈ Finset.range n, f i) := by
  have h0 : List.replicate W false = word W 0 := by
    rw [← Nat.cast_zero, word_natCast, toBitsLE_zero]
  rw [sumWords, h0]
  refine loopN_semiconj (word W) _ (fun i a => a + f i) 0 n (fun i hi => by
    rw [he i (by omega), wadd_word]) |>.trans ?_
  congr 1
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [loopN_succ, ih fun i hi => he i (by omega), Finset.sum_range_succ]

theorem sumWords_mem_FP {W n : List Bool → ℕ} {e : List Bool → ℕ → List Bool} (hW : UnaryFn W)
    (hn : UnaryFn n) (he : (fun y => e (pairFst y) (pairSnd y).length) ∈ FP)
    (hlen : ∀ z i, (e z i).length = W z) :
    (fun z => sumWords (W z) (e z) (n z)) ∈ FP := by
  have he' : (fun q => e (pairFst (pairFst q)) (pairSnd q).length) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp (mem_FP_pair ctx₂_mem_FP (UnaryFn.idx.replicate_mem_FP true)) he)
      fun q => by simp
  exact loopN_mem_FP (step := fun z i acc => wadd acc (e z i))
    (wadd_mem_FP (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) he') (hW.replicate_mem_FP false)
    hn hW (fun z i s hs => by rw [length_wadd _ _ (by rw [hlen, hs]), hs]) fun z => by simp

/-- **A sum over a polynomial-time range is polynomial-time.** The summand `f z i` is given as
a word computed from `pair z (1^i)`. -/
theorem WordFn.sum {W n : List Bool → ℕ} {f : List Bool → ℕ → ℤ} (hW : UnaryFn W)
    (hn : UnaryFn n)
    (hf : WordFn (fun y => W (pairFst y)) fun y => f (pairFst y) (pairSnd y).length) :
    WordFn W fun z => ∑ i ∈ Finset.range (n z), f z i :=
  mem_FP_of_eq (sumWords_mem_FP (e := fun z i => word (W z) (f z i)) hW hn hf fun _ _ => by simp)
    fun _ => sumWords_eq fun _ _ => rfl

end LinearProgramming
