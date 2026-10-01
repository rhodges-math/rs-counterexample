import Schubert.LinearProgramming.Vectors.Loop

/-!
# Searching a range

The least index below `n` with a property (`LinearProgramming.firstIdx`) and the least index
below `n` at which a function is largest (`LinearProgramming.argmaxIdx`), with their
polynomial-time computability.

The tests in a search only need to be right at the indices below `n`. So the polynomial-time
versions take a test that is polynomial-time everywhere and agrees with the property below `n`
(`LinearProgramming.UnaryFn.firstIdx_of_iff`). Comparisons of words are tests of this kind: the
sign bit of a difference is always polynomial-time (`LinearProgramming.FPPred.msb_sub`), and it is
the comparison whenever the difference fits.

## Main definitions

* `LinearProgramming.firstIdx p n`: the least `j < n` with `p j`, or `n`.
* `LinearProgramming.argmaxIdx f n`: the least `j < n` at which `f j` is largest.

## Main results

* `LinearProgramming.firstIdx_lt_iff`, `LinearProgramming.firstIdx_spec`,
  `LinearProgramming.not_of_lt_firstIdx`: what the search finds.
* `LinearProgramming.argmaxIdx_lt`, `LinearProgramming.le_argmaxIdx`: the maximum.
* `LinearProgramming.UnaryFn.firstIdx_of_iff`, `LinearProgramming.UnaryFn.argmaxIdx`.
-/

namespace LinearProgramming

open Complexity

/-! ### The least index with a property -/

/-- The least `j < n` with `p j`, or `n` if there is none. -/
def firstIdx (p : ℕ → Prop) [DecidablePred p] (n : ℕ) : ℕ :=
  (List.range n).findIdx fun j => decide (p j)

variable {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q] {n : ℕ}

theorem firstIdx_le : firstIdx p n ≤ n := by
  have := List.findIdx_le_length (p := fun j => decide (p j)) (xs := List.range n)
  rwa [List.length_range] at this

theorem firstIdx_lt_iff : firstIdx p n < n ↔ ∃ j < n, p j := by
  have h := List.findIdx_lt_length (p := fun j => decide (p j)) (xs := List.range n)
  rw [List.length_range] at h
  rw [firstIdx, h]
  simp

theorem firstIdx_spec (h : firstIdx p n < n) : p (firstIdx p n) := by
  have hl : (List.range n).findIdx (fun j => decide (p j)) < (List.range n).length := by
    simpa [firstIdx] using h
  have := List.findIdx_getElem (w := hl)
  simpa [firstIdx] using this

theorem not_of_lt_firstIdx {i : ℕ} (hi : i < firstIdx p n) : ¬ p i := by
  have hin : i < (List.range n).length := by
    have := firstIdx_le (p := p) (n := n)
    simp only [List.length_range]
    omega
  have := List.not_of_lt_findIdx (p := fun j => decide (p j)) (xs := List.range n) hi
  simpa using this

theorem findIdx_congr {α : Type*} {r s : α → Bool} :
    ∀ l : List α, (∀ x ∈ l, r x = s x) → l.findIdx r = l.findIdx s
  | [], _ => rfl
  | x :: l, h => by
    rw [List.findIdx_cons, List.findIdx_cons, h x (by simp),
      findIdx_congr l fun y hy => h y (by simp [hy])]

theorem firstIdx_congr (h : ∀ j < n, p j ↔ q j) : firstIdx p n = firstIdx q n :=
  findIdx_congr _ fun j hj => by
    rw [decide_eq_decide]
    exact h j (List.mem_range.mp hj)

/-- **A search is polynomial-time** when its test is polynomial-time, as a function of
`pair z (1^j)`, at the indices below the polynomial-time bound `n z`. -/
theorem UnaryFn.firstIdx_of_iff {n : List Bool → ℕ} {p : List Bool → ℕ → Prop}
    [∀ z, DecidablePred (p z)] {r : List Bool → Prop} [DecidablePred r] (hn : UnaryFn n)
    (hr : FPPred r)
    (hrp : ∀ z, ∀ j < n z, r (pair z (List.replicate j true)) ↔ p z j) :
    UnaryFn fun z => firstIdx (p z) (n z) :=
  (UnaryFn.find hn hr).of_eq fun z => findIdx_congr _ fun j hj => by
    rw [decide_eq_decide]
    exact hrp z j (List.mem_range.mp hj)

/-! ### The least index of a maximum -/

/-- The least `j < n` at which `f j` is largest; `0` if `n = 0`. -/
def argmaxIdx (f : ℕ → ℤ) (n : ℕ) : ℕ := firstIdx (fun j => ∀ i < n, f i ≤ f j) n

theorem exists_isMax (f : ℕ → ℤ) (hn : 0 < n) : ∃ j < n, ∀ i < n, f i ≤ f j := by
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.range n) f ⟨0, by simpa using hn⟩
  exact ⟨j, by simpa using hj, fun i hi => hmax i (by simpa using hi)⟩

theorem argmaxIdx_lt (f : ℕ → ℤ) (hn : 0 < n) : argmaxIdx f n < n :=
  firstIdx_lt_iff.mpr (exists_isMax f hn)

/-- `f` is largest at `argmaxIdx f n`. -/
theorem le_argmaxIdx (f : ℕ → ℤ) {i : ℕ} (hi : i < n) : f i ≤ f (argmaxIdx f n) :=
  firstIdx_spec (argmaxIdx_lt f (by omega)) i hi

/-! ### Comparisons as tests -/

theorem WordFn.congr {W W' : List Bool → ℕ} {v v' : List Bool → ℤ} (hv : WordFn W v)
    (hW : ∀ z, W z = W' z) (hv' : ∀ z, v z = v' z) : WordFn W' v' :=
  mem_FP_of_eq hv fun z => by rw [hW z, hv' z]

/-- The sign bit of a difference of polynomial-time words is a polynomial-time test, whether or
not the difference fits. -/
theorem FPPred.msb_sub {W : List Bool → ℕ} {v w : List Bool → ℤ} (hv : WordFn W v)
    (hw : WordFn W w) : FPPred fun z => msb (word (W z) (v z - w z)) = true :=
  FPPred.of_flag (msb_mem_FP (hv.sub hw))

/-- A family of words indexed by `pair z (1^i)`, read at the inner index of
`pair (pair z (1^j)) (1^i)`. -/
theorem WordFn.inner {W : List Bool → ℕ} {f : List Bool → ℕ → ℤ}
    (hf : WordFn (fun y => W (pairFst y)) fun y => f (pairFst y) (pairSnd y).length) :
    WordFn (fun x => W (pairFst (pairFst x))) fun x => f (pairFst (pairFst x)) (pairSnd x).length :=
  (hf.comp (mem_FP_pair ctx₂_mem_FP pairSnd_mem_FP)).congr (fun x => by simp)
    fun x => by simp

/-- A family of words indexed by `pair z (1^j)`, read at the outer index of
`pair (pair z (1^j)) (1^i)`. -/
theorem WordFn.outer {W : List Bool → ℕ} {f : List Bool → ℕ → ℤ}
    (hf : WordFn (fun y => W (pairFst y)) fun y => f (pairFst y) (pairSnd y).length) :
    WordFn (fun x => W (pairFst (pairFst x))) fun x =>
      f (pairFst (pairFst x)) (pairSnd (pairFst x)).length :=
  hf.comp pairFst_mem_FP

/-- **The least index of a maximum is polynomial-time**, for a polynomial-time family of words
whose differences below `n` fit. -/
theorem UnaryFn.argmaxIdx {W n : List Bool → ℕ} {f : List Bool → ℕ → ℤ} (hn : UnaryFn n)
    (hf : WordFn (fun y => W (pairFst y)) fun y => f (pairFst y) (pairSnd y).length)
    (hfit : ∀ z, ∀ i < n z, ∀ j < n z, Fits (W z) (f z j - f z i)) :
    UnaryFn fun z => argmaxIdx (f z) (n z) := by
  have hnc : UnaryFn fun y => n (pairFst y) := hn.comp pairFst_mem_FP
  have hlt := FPPred.msb_sub hf.outer hf.inner
  refine UnaryFn.firstIdx_of_iff hn (FPPred.forall_lt hnc hlt.not) fun z j hj => ?_
  simp only [pairFst_pair, pairSnd_pair, List.length_replicate]
  refine forall_congr' fun i => imp_congr_right fun hi => ?_
  rw [msb_word (hfit z i hi j hj)]
  simp

end LinearProgramming
