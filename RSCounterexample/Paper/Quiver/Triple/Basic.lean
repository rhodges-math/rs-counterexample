import RSCounterexample.Paper.Window.Basic
import Mathlib.Combinatorics.Enumerative.Composition

/-!
# Quiver triples

Definition 5.1 of the paper. An interval partition of `{0, …, n − 1}` into nonempty consecutive
intervals `I_0 < ⋯ < I_{s−1}` is a composition of `n` in Mathlib's sense (`_root_.Composition n`,
the list of block sizes): block `p` is the range of `I.embedding p`, and `I.index i` is the block
containing `i`.

A triple of weak compositions `(a, b, c)` with `|a| + |b| = |c|` is a *quiver triple* if, for some
`N ≥ max c` and `c̄ = N·1 − c`, there is an interval partition such that

1. each of `a`, `b`, `c̄` is weakly decreasing on every interval;
2. for every pair of intervals `I_p`, `I_q` with `p < q`, the comparison weight
   `cmp((a_i, b_i, c̄_i), (a_j, b_j, c̄_j))` has the same nonnegative value for all `i ∈ I_p`,
   `j ∈ I_q`;
3. all prefix heights are nonnegative and the window inequalities (2.12) hold.

The conditions do not depend on `N` (`isQuiverPartition_iff_of_le`).

## Main definitions

* `Schubert.RS.Quiver.IntervalPartition`: interval partitions, as Mathlib compositions.
* `Schubert.RS.Quiver.IsQuiverPartition`: Definition 5.1 for a given partition and `N`.
* `Schubert.RS.Quiver.IsQuiverTriple`: Definition 5.1, with `N = max c`.
-/

namespace Schubert.RS.Quiver

/-- An interval partition of `{0, …, n − 1}` into nonempty consecutive intervals: a composition of
`n` (Mathlib's `Composition`, the list of block sizes). -/
abbrev IntervalPartition (n : ℕ) : Type := _root_.Composition n

variable {n : ℕ}

namespace IntervalPartition

variable (I : IntervalPartition n)

/-- The positions of a block form an interval: blocks are listed in increasing order. -/
theorem embedding_lt_embedding {p q : Fin I.length} (hpq : p < q) (k : Fin (I.blocksFun p))
    (l : Fin (I.blocksFun q)) : I.embedding p k < I.embedding q l := by
  rw [Fin.lt_def, _root_.Composition.coe_embedding, _root_.Composition.coe_embedding]
  have h1 : I.sizeUpTo p + I.blocksFun p = I.sizeUpTo (p + 1) :=
    (I.sizeUpTo_succ' p).symm
  have h2 : I.sizeUpTo (p + 1) ≤ I.sizeUpTo q := I.monotone_sizeUpTo (Nat.succ_le_of_lt hpq)
  have := k.isLt
  omega

/-- Block indices are weakly increasing. -/
theorem index_mono {i j : Fin n} (hij : i ≤ j) : I.index i ≤ I.index j := by
  by_contra h
  push Not at h
  have h1 := I.sizeUpTo_index_le i
  have h2 := I.lt_sizeUpTo_index_succ j
  have h3 : I.sizeUpTo ((I.index j : ℕ) + 1) ≤ I.sizeUpTo (I.index i) :=
    I.monotone_sizeUpTo (Nat.succ_le_of_lt h)
  have : (i : ℕ) ≤ j := hij
  simp only [Fin.val_succ] at h2
  omega

/-- The first position of block `p`. -/
def first (p : Fin I.length) : Fin n := I.embedding p ⟨0, I.one_le_blocksFun p⟩

end IntervalPartition

/-- **Definition 5.1** for a given interval partition `I` and a given `N ≥ max c`: conditions (i),
(ii) and (iii) of the paper, with (iii) and the degree equality packaged in
`Window.Hypotheses`. -/
structure IsQuiverPartition (a b c : Composition n) (N : ℕ) (I : IntervalPartition n) : Prop where
  /-- The degree equality, `N ≥ max c`, nonnegative prefix heights and the window inequalities. -/
  hyp : Window.Hypotheses a b c N
  /-- (i) Each of `a`, `b`, `c̄` is weakly decreasing on every interval. -/
  antitone : ∀ i j : Fin n, i ≤ j → I.index i = I.index j →
    a j ≤ a i ∧ b j ≤ b i ∧ Window.complement N c j ≤ Window.complement N c i
  /-- (ii) Across two intervals the comparison weight is constant and nonnegative. -/
  cmp_const : ∀ p q : Fin I.length, p < q → ∃ k : ℕ, ∀ i j : Fin n,
    I.index i = p → I.index j = q →
      Window.cmp (Window.triple a b (Window.complement N c) i)
        (Window.triple a b (Window.complement N c) j) = k

/-- **Definition 5.1**: `(a, b, c)` is a quiver triple if some interval partition satisfies the
conditions, for `N = max c` (equivalently for every `N ≥ max c`, by
`isQuiverTriple_iff_of_le`). -/
def IsQuiverTriple (a b c : Composition n) : Prop :=
  ∃ I : IntervalPartition n, IsQuiverPartition a b c (Finset.univ.sup c) I

theorem le_sup (c : Composition n) (i : Fin n) : c i ≤ Finset.univ.sup c :=
  Finset.le_sup (Finset.mem_univ i)

/-- The conditions of Definition 5.1 do not depend on `N ≥ max c` (the remark after the
definition). -/
theorem isQuiverPartition_iff_of_le {a b c : Composition n} {N N' : ℕ} {I : IntervalPartition n}
    (hN : ∀ i, c i ≤ N) (hN' : ∀ i, c i ≤ N') :
    IsQuiverPartition a b c N I ↔ IsQuiverPartition a b c N' I := by
  have hc : ∀ i j, (Window.complement N c j ≤ Window.complement N c i) ↔
      (Window.complement N' c j ≤ Window.complement N' c i) := by
    intro i j
    have := hN i
    have := hN j
    have := hN' i
    have := hN' j
    simp only [Window.complement]
    omega
  constructor
  · intro h
    refine ⟨(Window.hypotheses_iff_of_le hN hN').1 h.hyp, fun i j hij hb => ?_, fun p q hpq => ?_⟩
    · obtain ⟨ha, hb', hc'⟩ := h.antitone i j hij hb
      exact ⟨ha, hb', (hc i j).1 hc'⟩
    · obtain ⟨k, hk⟩ := h.cmp_const p q hpq
      exact ⟨k, fun i j hi hj => by rw [← Window.cmp_complement_eq a b hN hN', hk i j hi hj]⟩
  · intro h
    refine ⟨(Window.hypotheses_iff_of_le hN hN').2 h.hyp, fun i j hij hb => ?_, fun p q hpq => ?_⟩
    · obtain ⟨ha, hb', hc'⟩ := h.antitone i j hij hb
      exact ⟨ha, hb', (hc i j).2 hc'⟩
    · obtain ⟨k, hk⟩ := h.cmp_const p q hpq
      exact ⟨k, fun i j hi hj => by rw [Window.cmp_complement_eq a b hN hN', hk i j hi hj]⟩

theorem isQuiverTriple_iff_of_le {a b c : Composition n} {N : ℕ} (hN : ∀ i, c i ≤ N) :
    IsQuiverTriple a b c ↔ ∃ I : IntervalPartition n, IsQuiverPartition a b c N I :=
  exists_congr fun _ => isQuiverPartition_iff_of_le (le_sup c) hN

/-- Within an interval the comparison weight is `−1`. -/
theorem IsQuiverPartition.cmp_eq_neg_one {a b c : Composition n} {N : ℕ} {I : IntervalPartition n}
    (h : IsQuiverPartition a b c N I) {i j : Fin n} (hij : i < j) (hb : I.index i = I.index j) :
    Window.cmp (Window.triple a b (Window.complement N c) i)
      (Window.triple a b (Window.complement N c) j) = -1 := by
  obtain ⟨ha, hb', hc⟩ := h.antitone i j hij.le hb
  simp only [Window.cmp, Window.triple, not_lt.mpr ha, not_lt.mpr hb', not_lt.mpr hc,
    ↓reduceIte]
  norm_num

end Schubert.RS.Quiver
