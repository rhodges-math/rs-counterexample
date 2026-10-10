import RSCounterexample.Paper.Quiver.Polytope.LatticeSlots
import RSCounterexample.Paper.Quiver.Polytope.Decode
import RSCounterexample.Paper.Quiver.OfTriple
import RSCounterexample.Paper.Quiver.Triple.Canonical

/-!
# The positional data of a triple realizes its canonical quiver

For lists `a, b, c` (of length `n = c.length`, read as weak compositions padded with zeros), the
positional data `Schubert.RS.Quiver.Flat.positionalOf a b c` describes the quiver of Theorem 5.3
for the canonical interval partition `I` of the triple
(`Schubert.RS.Quiver.canonicalPartition`): the starting positions of `positionalOf` are the first
positions of the intervals of `I`, its block dimensions are their lengths, and its arrow numbers are
the comparison weights. With any weight `w` that agrees with a weight `λ` of the quiver at the
vertices, `positionalOf a b c` realizes the quiver with `λ`
(`Schubert.RS.Quiver.Flat.realizes_positionalOf`).

## Main definitions

* `Schubert.RS.Quiver.Flat.listComp`: a list as a weak composition of a given length.
* `Schubert.RS.Quiver.Flat.canonicalQuiver`, `Schubert.RS.Quiver.Flat.canonicalWeight`: the quiver
  of Theorem 5.3 of the triple, for the canonical partition and `N = max c`, and its weight.

## Main results

* `Schubert.RS.Quiver.Flat.isStart_iff_exists_first`: the starting positions are the first positions
  of the intervals.
* `Schubert.RS.Quiver.Flat.blockDim_first`, `Schubert.RS.Quiver.Flat.arrowCount_first`.
* `Schubert.RS.Quiver.Flat.realizes_positionalOf`.
-/

namespace Schubert.RS.Quiver.Flat

open Finset

/-- A list as a weak composition of length `n`: the entries beyond the list are `0`. -/
abbrev listComp (n : ℕ) (x : List ℕ) : Composition n := fun i => entry x i

variable (a b c : List ℕ)

/-- The canonical interval partition of the triple of lists. -/
abbrev canonicalPart : IntervalPartition c.length :=
  canonicalPartition (listComp c.length a) (listComp c.length b) (listComp c.length c)

/-- **The quiver of Theorem 5.3 of the triple of lists**: the quiver of the canonical partition,
with `N = max c`. -/
abbrev canonicalQuiver : ForwardQuiver :=
  quiverOf (listComp c.length a) (listComp c.length b) (listComp c.length c)
    (Finset.univ.sup (listComp c.length c)) (canonicalPart a b c)

/-- The weight `(λ^{(p)})_p` of the canonical quiver. -/
abbrev canonicalWeight : (canonicalQuiver a b c).Weight :=
  leviWeight (listComp c.length a) (listComp c.length b) (listComp c.length c)
    (canonicalPart a b c)

theorem first_val (p : Fin (canonicalPart a b c).length) :
    ((canonicalPart a b c).first p : ℕ) = (canonicalPart a b c).sizeUpTo p := by
  simp [IntervalPartition.first, _root_.Composition.coe_embedding]

theorem boundaries_canonicalPart :
    (canonicalPart a b c).boundaries =
      canonicalBoundaries (listComp c.length a) (listComp c.length b) (listComp c.length c) :=
  CompositionAsSet.toComposition_boundaries _

/-- **The starting positions are the first positions of the intervals** of the canonical
partition. -/
theorem isStart_iff_exists_first {i : ℕ} (hi : i < c.length) :
    isStart a b c i = true ↔ ∃ p, ((canonicalPart a b c).first p : ℕ) = i := by
  have h1 : (∃ p : Fin (canonicalPart a b c).length, ((canonicalPart a b c).first p : ℕ) = i) ↔
      (⟨i, by omega⟩ : Fin (c.length + 1)) ∈ (canonicalPart a b c).boundaries := by
    rw [IntervalPartition.mem_boundaries_iff]
    constructor
    · rintro ⟨p, hp⟩
      refine ⟨p.castSucc, ?_⟩
      change (canonicalPart a b c).sizeUpTo p = i
      rw [← first_val]
      exact hp
    · rintro ⟨q, hq⟩
      have hql : (q : ℕ) < (canonicalPart a b c).length := by
        by_contra hge
        have : (q : ℕ) = (canonicalPart a b c).length := by have := q.isLt; omega
        rw [this, _root_.Composition.sizeUpTo_length] at hq
        change c.length = i at hq
        omega
      exact ⟨⟨q, hql⟩, by rw [first_val]; exact hq⟩
  rw [h1, boundaries_canonicalPart, canonicalBoundaries, mem_filter]
  simp only [mem_univ, true_and]
  unfold isStart riseAt
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · rintro (h0 | ⟨hpos, h⟩)
    · exact Or.inl h0
    · refine Or.inr (Or.inr ⟨⟨i - 1, by omega⟩, by simp only; omega, by simp only; omega, ?_⟩)
      have e : (⟨(⟨i - 1, by omega⟩ : Fin c.length).val + 1, by simp only; omega⟩ :
          Fin c.length) = ⟨i, hi⟩ := Fin.ext (by simp only; omega)
      unfold Rises
      rw [e]
      simpa only [listComp, or_assoc] using h
  · rintro (h0 | hn | ⟨i', hi', hii, hr⟩)
    · exact Or.inl h0
    · omega
    · right
      refine ⟨by omega, ?_⟩
      have e1 : i - 1 = i' := by omega
      have e2 : (⟨i'.val + 1, hi'⟩ : Fin c.length) = ⟨i, hi⟩ := Fin.ext (by simp only; omega)
      unfold Rises at hr
      rw [e2] at hr
      simpa only [listComp, e1, or_assoc] using hr

theorem first_lt (p : Fin (canonicalPart a b c).length) :
    ((canonicalPart a b c).first p : ℕ) < c.length :=
  ((canonicalPart a b c).first p).isLt

theorem first_strictMono : StrictMono fun p => ((canonicalPart a b c).first p : ℕ) := by
  intro p q hpq
  simp only [first_val]
  exact lt_of_lt_of_le ((canonicalPart a b c).sizeUpTo_strict_mono p.isLt)
    ((canonicalPart a b c).monotone_sizeUpTo (Nat.succ_le_of_lt hpq))

theorem first_add_blocksFun (p : Fin (canonicalPart a b c).length) :
    ((canonicalPart a b c).first p : ℕ) + (canonicalPart a b c).blocksFun p =
      (canonicalPart a b c).sizeUpTo (p + 1) := by
  rw [first_val, (canonicalPart a b c).sizeUpTo_succ' p]

/-- The positions strictly inside an interval start no interval. -/
theorem not_isStart_of_lt {p : Fin (canonicalPart a b c).length} {j : ℕ}
    (h1 : ((canonicalPart a b c).first p : ℕ) < j)
    (h2 : j < (canonicalPart a b c).sizeUpTo (p + 1)) : isStart a b c j = false := by
  have hj : j < c.length := lt_of_lt_of_le h2 ((canonicalPart a b c).sizeUpTo_le _)
  rw [← Bool.not_eq_true, isStart_iff_exists_first a b c hj]
  rintro ⟨q, hq⟩
  rw [first_val] at hq h1
  rcases le_or_gt q p with hqp | hqp
  · have := (canonicalPart a b c).monotone_sizeUpTo (show (q : ℕ) ≤ p from hqp)
    omega
  · have := (canonicalPart a b c).monotone_sizeUpTo (show (p : ℕ) + 1 ≤ q from hqp)
    omega

/-- **The block dimensions are the lengths of the intervals.** -/
theorem blockDim_first (p : Fin (canonicalPart a b c).length) :
    blockDim a b c ((canonicalPart a b c).first p) = (canonicalPart a b c).blocksFun p := by
  have hd : 0 < (canonicalPart a b c).blocksFun p := (canonicalPart a b c).one_le_blocksFun p
  have hid := first_add_blocksFun a b c p
  have hle : (canonicalPart a b c).sizeUpTo (p + 1) ≤ c.length :=
    (canonicalPart a b c).sizeUpTo_le _
  have hinside : ∀ j, ((canonicalPart a b c).first p : ℕ) < j →
      j < (canonicalPart a b c).sizeUpTo (p + 1) → isStart a b c j = false :=
    fun j h1 h2 => not_isStart_of_lt a b c h1 h2
  have hnext : (canonicalPart a b c).sizeUpTo (p + 1) < c.length →
      isStart a b c ((canonicalPart a b c).sizeUpTo (p + 1)) = true := by
    intro hlt
    have hp1 : (p : ℕ) + 1 < (canonicalPart a b c).length := by
      by_contra hge
      have : (p : ℕ) + 1 = (canonicalPart a b c).length := by have := p.isLt; omega
      rw [this, _root_.Composition.sizeUpTo_length] at hlt
      omega
    rw [isStart_iff_exists_first a b c hlt]
    exact ⟨⟨(p : ℕ) + 1, hp1⟩, by rw [first_val]⟩
  generalize ((canonicalPart a b c).first p : ℕ) = i at hid hinside ⊢
  generalize (canonicalPart a b c).sizeUpTo (p + 1) = e at hid hle hinside hnext
  generalize (canonicalPart a b c).blocksFun p = d at hd hid ⊢
  have key : ∀ t ∈ List.range (c.length - (i + 1)),
      ((List.range (t + 1)).all fun s => !isStart a b c (i + 1 + s)) = decide (t < d - 1) := by
    intro t ht
    rw [List.mem_range] at ht
    by_cases htd : t < d - 1
    · rw [decide_eq_true htd, List.all_eq_true]
      intro s hs
      rw [List.mem_range] at hs
      rw [hinside _ (by omega) (by omega)]
      rfl
    · rw [decide_eq_false htd, List.all_eq_false]
      refine ⟨d - 1, List.mem_range.mpr (by omega), ?_⟩
      have hst : isStart a b c (i + 1 + (d - 1)) = true := by
        rw [show i + 1 + (d - 1) = e by omega]
        exact hnext (by omega)
      simp [hst]
  unfold blockDim
  rw [List.filter_congr key]
  have hsplit : List.range (c.length - (i + 1)) =
      List.range' 0 (d - 1) ++ List.range' (d - 1) (c.length - (i + 1) - (d - 1)) := by
    have h := List.range'_append (s := 0) (m := d - 1) (n := c.length - (i + 1) - (d - 1))
      (step := 1)
    rw [show 0 + 1 * (d - 1) = d - 1 by omega,
      show d - 1 + (c.length - (i + 1) - (d - 1)) = c.length - (i + 1) by omega] at h
    rw [List.range_eq_range', h]
  rw [hsplit, List.filter_append, List.filter_eq_self.mpr, List.filter_eq_nil_iff.mpr]
  · simp only [List.append_nil, List.length_range']
    omega
  · intro t ht
    rw [List.mem_range'_1] at ht
    simp only [decide_eq_true_eq]
    omega
  · intro t ht
    rw [List.mem_range'_1] at ht
    simp only [decide_eq_true_eq]
    omega

theorem blocksFun_le (p : Fin (canonicalPart a b c).length) :
    (canonicalPart a b c).blocksFun p ≤ c.length := by
  have h1 := first_add_blocksFun a b c p
  have h2 := (canonicalPart a b c).sizeUpTo_le (p + 1)
  omega

/-- **The arrow numbers are the comparison weights** of the canonical quiver. -/
theorem arrowCount_first (p q : Fin (canonicalPart a b c).length) :
    arrowCount a b c ((canonicalPart a b c).first p) ((canonicalPart a b c).first q) =
      (canonicalQuiver a b c).arrows p q := by
  have hs : ∀ p : Fin (canonicalPart a b c).length,
      isStart a b c ((canonicalPart a b c).first p) = true :=
    fun p => (isStart_iff_exists_first a b c (first_lt a b c p)).mpr ⟨p, rfl⟩
  rw [quiverOf_arrows]
  unfold arrowCount
  rw [hs p, hs q]
  by_cases hpq : p < q
  · have hlt := first_strictMono a b c hpq
    simp only [Bool.true_and, hlt, decide_true, ↓reduceIte, hpq]
    congr 1
    unfold cmpAt Window.cmp Window.triple Window.complement
    have h1 := Quiver.le_sup (listComp c.length c) ((canonicalPart a b c).first p)
    have h2 := Quiver.le_sup (listComp c.length c) ((canonicalPart a b c).first q)
    have e : (Finset.univ.sup (listComp c.length c) - listComp c.length c
          ((canonicalPart a b c).first p) <
        Finset.univ.sup (listComp c.length c) - listComp c.length c
          ((canonicalPart a b c).first q)) ↔
        entry c ((canonicalPart a b c).first q) < entry c ((canonicalPart a b c).first p) := by
      simp only [listComp] at h1 h2 ⊢
      omega
    simp only [listComp] at e ⊢
    rw [if_congr e rfl rfl]
  · have hle : ¬ ((canonicalPart a b c).first p : ℕ) < (canonicalPart a b c).first q := by
      intro h
      exact hpq ((first_strictMono a b c).lt_iff_lt.mp h)
    simp only [Bool.true_and, hle, decide_false, Bool.false_eq_true, ↓reduceIte, hpq]

theorem canonicalQuiver_arrows_le_two (p q : Fin (canonicalPart a b c).length) :
    (canonicalQuiver a b c).arrows p q ≤ 2 := by
  rw [← arrowCount_first]
  exact arrowCount_le_two a b c _ _

/-- **The positional data of a triple realizes its canonical quiver**, with any weight `w` that
agrees with the weight `λ` of the quiver at the vertices. -/
def realizes_positionalOf (w : ℕ → ℕ → ℤ) (lam : (canonicalQuiver a b c).Weight)
    (hw : ∀ p (l : Fin ((canonicalQuiver a b c).dim p)),
      w ((canonicalPart a b c).first p) l = lam p l) :
    ((positionalOf a b c).withWeight w).Realizes (canonicalQuiver a b c) lam where
  st p := (canonicalPart a b c).first p
  st_strictMono := first_strictMono a b c
  st_lt p := first_lt a b c p
  isStart_iff i hi := isStart_iff_exists_first a b c hi
  blockDim_st p := blockDim_first a b c p
  dim_le p := blocksFun_le a b c p
  arrowCount_st p q := arrowCount_first a b c p q
  exists_of_arrowCount_ne_zero i hi j hj h := by
    obtain ⟨-, h1, h2⟩ := lt_of_arrowCount_pos a b c (Nat.pos_of_ne_zero h)
    obtain ⟨p, hp⟩ := (isStart_iff_exists_first a b c hi).mp h1
    obtain ⟨q, hq⟩ := (isStart_iff_exists_first a b c hj).mp h2
    exact ⟨p, q, hp, hq⟩
  arrows_le_two p q := canonicalQuiver_arrows_le_two a b c p q
  weight_st p l := hw p l

/-- The weight of `positionalOf a b c` agrees with the weight of the canonical quiver at the
vertices. -/
theorem weight_positionalOf_first (p : Fin (canonicalPart a b c).length)
    (l : Fin ((canonicalQuiver a b c).dim p)) :
    (positionalOf a b c).weight ((canonicalPart a b c).first p) l = canonicalWeight a b c p l := by
  change nu a b c (_ + blockDim a b c _ - 1 - _) = _
  rw [blockDim_first]
  change _ = Window.residual (listComp c.length a) (listComp c.length b) (listComp c.length c)
    ((canonicalPart a b c).embedding p (Fin.rev l))
  unfold nu Window.residual
  have e : ((canonicalPart a b c).embedding p (Fin.rev l) : ℕ) =
      ((canonicalPart a b c).first p : ℕ) + (canonicalPart a b c).blocksFun p - 1 - l := by
    have hl' : (l : ℕ) < (canonicalPart a b c).blocksFun p := l.isLt
    rw [_root_.Composition.coe_embedding, first_val, Fin.val_rev]
    omega
  simp only [listComp, e]

end Schubert.RS.Quiver.Flat
