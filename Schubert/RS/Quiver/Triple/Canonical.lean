import Schubert.RS.Quiver.Triple.Basic
import Schubert.RS.Window.General

/-!
# The canonical interval partition

The paper's recognition argument for quiver triples (lines 1879–1893): an interval partition
witnessing Definition 5.1 has a cut between positions `i` and `i + 1` exactly when one of `a`, `b`
strictly increases or `c` strictly decreases there. Inside an interval this cannot happen, since
`a`, `b`, `c̄` are weakly decreasing there; across a cut it must happen, since otherwise the
comparison weight of the two positions is `−1`. So the partition is unique: it is the canonical
partition cut at these positions, and being a quiver triple is decidable.

## Main definitions

* `Schubert.RS.Quiver.Rises`: one of `a`, `b` strictly increases or `c` strictly decreases.
* `Schubert.RS.Quiver.canonicalPartition`: the interval partition cut at the rises.

## Main results

* `Schubert.RS.Quiver.IsQuiverPartition.eq_canonical`: a quiver partition is the canonical one.
* `Schubert.RS.Quiver.isQuiverTriple_iff_canonical`.
* `Schubert.RS.Quiver.instDecidableIsQuiverTriple`: being a quiver triple is decidable.
-/

namespace Schubert.RS.Quiver

variable {n : ℕ}

/-- Between positions `i` and `j`, `a` or `b` strictly increases, or `c` strictly decreases (so that
`c̄ = N·1 − c` strictly increases). -/
def Rises (a b c : Composition n) (i j : Fin n) : Prop := a i < a j ∨ b i < b j ∨ c j < c i

instance (a b c : Composition n) : DecidableRel (Rises a b c) := fun _ _ => by
  unfold Rises
  infer_instance

namespace IntervalPartition

variable (I : IntervalPartition n)

theorem mem_boundaries_iff (j : Fin (n + 1)) :
    j ∈ I.boundaries ↔ ∃ q : Fin (I.length + 1), I.sizeUpTo q = j.val := by
  simp [_root_.Composition.boundaries, _root_.Composition.boundary, Fin.ext_iff]

/-- Position `i + 1` starts a new interval exactly when `i` and `i + 1` lie in different
intervals. -/
theorem succ_mem_boundaries_iff (i : Fin n) (h : i.val + 1 < n) :
    (⟨i.val + 1, by omega⟩ : Fin (n + 1)) ∈ I.boundaries ↔
      I.index i ≠ I.index ⟨i.val + 1, h⟩ := by
  rw [mem_boundaries_iff]
  constructor
  · rintro ⟨q, hq⟩ heq
    have h1 := I.sizeUpTo_index_le i
    have h2 := I.lt_sizeUpTo_index_succ ⟨i.val + 1, h⟩
    simp only [Fin.val_succ] at h2
    rw [← heq] at h2
    rcases le_or_gt (q : ℕ) (I.index i : ℕ) with hle | hlt
    · have := I.monotone_sizeUpTo hle
      simp only at hq
      omega
    · have := I.monotone_sizeUpTo (show (I.index i : ℕ) + 1 ≤ q from hlt)
      simp only at hq
      omega
  · intro hne
    have hmono := I.index_mono (show i ≤ ⟨i.val + 1, h⟩ from Fin.le_def.mpr (Nat.le_succ _))
    have hlt : I.index i < I.index ⟨i.val + 1, h⟩ := lt_of_le_of_ne hmono hne
    have h1 := I.lt_sizeUpTo_index_succ i
    have h2 := I.sizeUpTo_index_le ⟨i.val + 1, h⟩
    have h3 : I.sizeUpTo ((I.index i : ℕ) + 1) ≤ I.sizeUpTo (I.index ⟨i.val + 1, h⟩) :=
      I.monotone_sizeUpTo (Nat.succ_le_of_lt hlt)
    simp only [Fin.val_succ] at h1
    refine ⟨⟨(I.index i : ℕ) + 1, by have := (I.index ⟨i.val + 1, h⟩).isLt; omega⟩, ?_⟩
    simp only at h2 ⊢
    omega

end IntervalPartition

/-- The boundaries of the canonical partition: `0`, `n`, and every `i + 1` such that the triple
rises from `i` to `i + 1`. -/
def canonicalBoundaries (a b c : Composition n) : Finset (Fin (n + 1)) :=
  Finset.univ.filter fun j => j.val = 0 ∨ j.val = n ∨
    ∃ i : Fin n, ∃ h : i.val + 1 < n, i.val + 1 = j.val ∧ Rises a b c i ⟨i.val + 1, h⟩

/-- The canonical partition as a set of boundaries. -/
def canonicalAsSet (a b c : Composition n) : CompositionAsSet n where
  boundaries := canonicalBoundaries a b c
  zero_mem := by simp [canonicalBoundaries]
  getLast_mem := by simp [canonicalBoundaries]

/-- **The canonical interval partition** of a triple: cut between `i` and `i + 1` exactly when `a`
or `b` strictly increases or `c` strictly decreases there. -/
def canonicalPartition (a b c : Composition n) : IntervalPartition n :=
  (canonicalAsSet a b c).toComposition

/-- An interval partition whose cuts are the rises of the triple is the canonical one. -/
theorem eq_canonicalPartition {a b c : Composition n} (I : IntervalPartition n)
    (h : ∀ (i : Fin n) (hi : i.val + 1 < n),
      I.index i ≠ I.index ⟨i.val + 1, hi⟩ ↔ Rises a b c i ⟨i.val + 1, hi⟩) :
    I = canonicalPartition a b c := by
  have hset : I.toCompositionAsSet = canonicalAsSet a b c := by
    apply CompositionAsSet.ext
    ext j
    rw [_root_.Composition.toCompositionAsSet_boundaries]
    change j ∈ I.boundaries ↔ j ∈ canonicalBoundaries a b c
    rcases Nat.eq_zero_or_pos j.val with h0 | hpos
    · have hj : j = 0 := Fin.ext h0
      subst hj
      simp only [canonicalBoundaries, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_zero,
        true_or, iff_true]
      exact I.toCompositionAsSet.zero_mem
    rcases Nat.lt_or_ge j.val n with hlt | hge
    · have hi : j.val - 1 + 1 < n := by omega
      have hj : j = ⟨(⟨j.val - 1, by omega⟩ : Fin n).val + 1, by simp only; omega⟩ := by
        ext
        simp only
        omega
      rw [hj, IntervalPartition.succ_mem_boundaries_iff I ⟨j.val - 1, by omega⟩ hi,
        h ⟨j.val - 1, by omega⟩ hi]
      simp only [canonicalBoundaries, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hr
        exact Or.inr (Or.inr ⟨⟨j.val - 1, by omega⟩, hi, rfl, hr⟩)
      · rintro (h0 | hn | ⟨i, hi', hij, hr⟩)
        · omega
        · omega
        · obtain ⟨iv, hiv⟩ := i
          simp only at hij
          obtain rfl : iv = j.val - 1 := by omega
          exact hr
    · have hj : j = Fin.last n := Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega)
      subst hj
      simp only [canonicalBoundaries, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_last,
        or_true, true_or, iff_true]
      exact I.toCompositionAsSet.getLast_mem
  rw [canonicalPartition, ← hset]
  exact ((compositionEquiv n).left_inv I).symm

/-- **The partition of a quiver triple is unique** (the paper's recognition argument): it is the
canonical partition. -/
theorem IsQuiverPartition.eq_canonical {a b c : Composition n} {N : ℕ} {I : IntervalPartition n}
    (h : IsQuiverPartition a b c N I) : I = canonicalPartition a b c := by
  apply eq_canonicalPartition
  intro i hi
  have hN := h.hyp.le_N
  have hci := hN i
  have hcj := hN ⟨i.val + 1, hi⟩
  have hle : i ≤ ⟨i.val + 1, hi⟩ := Fin.le_def.mpr (Nat.le_succ _)
  constructor
  · intro hne
    by_contra hr
    simp only [Rises, not_or, not_lt] at hr
    obtain ⟨ha, hb, hc⟩ := hr
    have hlt : I.index i < I.index ⟨i.val + 1, hi⟩ := lt_of_le_of_ne (I.index_mono hle) hne
    obtain ⟨k, hk⟩ := h.cmp_const _ _ hlt
    have hcmp := hk i ⟨i.val + 1, hi⟩ rfl rfl
    have hc' : ¬ Window.complement N c i < Window.complement N c ⟨i.val + 1, hi⟩ := by
      simp only [Window.complement]
      omega
    simp only [Window.cmp, Window.triple, not_lt.mpr ha, not_lt.mpr hb, hc', ↓reduceIte] at hcmp
    omega
  · intro hr heq
    obtain ⟨ha, hb, hc⟩ := h.antitone i ⟨i.val + 1, hi⟩ hle heq
    simp only [Window.complement] at hc
    simp only [Rises] at hr
    omega

/-- **Recognition of quiver triples**: a triple is a quiver triple exactly when the canonical
partition is a quiver partition. -/
theorem isQuiverTriple_iff_canonical {a b c : Composition n} :
    IsQuiverTriple a b c ↔
      IsQuiverPartition a b c (Finset.univ.sup c) (canonicalPartition a b c) := by
  constructor
  · rintro ⟨I, hI⟩
    rwa [← hI.eq_canonical]
  · intro h
    exact ⟨_, h⟩

/-! ## Decidability -/

section Decidable

variable (a b c : Composition n) (N : ℕ) (I : IntervalPartition n)

/-- The window inequality with the cut index bounded by `n`. -/
def WindowInequalityFin (u : Composition n) : Prop :=
  ∀ i j : Fin n, i < j → u i < u j →
    ∃ k : Fin n, i.val ≤ k.val ∧ k.val < j.val ∧
      Window.prefixHeight a b c (k.val + 1) < (u j : ℤ) - u i + 1

theorem windowInequality_iff_fin (u : Composition n) :
    Window.WindowInequality u (Window.prefixHeight a b c) ↔ WindowInequalityFin a b c u := by
  constructor
  · intro hw i j hij hu
    obtain ⟨k, hk1, hk2, hk3⟩ := hw i j hij hu
    exact ⟨⟨k, by omega⟩, hk1, hk2, hk3⟩
  · intro hw i j hij hu
    obtain ⟨k, hk1, hk2, hk3⟩ := hw i j hij hu
    exact ⟨k.val, hk1, hk2, hk3⟩

theorem heightNonneg_iff_fin :
    (∀ k : ℕ, 0 ≤ Window.prefixHeight a b c k) ↔
      ∀ k : Fin (n + 1), 0 ≤ Window.prefixHeight a b c k.val := by
  constructor
  · exact fun h k => h k
  · intro h k
    rcases Nat.lt_or_ge k (n + 1) with hk | hk
    · exact h ⟨k, hk⟩
    · rw [Window.prefixHeight_of_le a b c (by omega : n ≤ k),
        ← Window.prefixHeight_of_le a b c (le_refl n)]
      exact h ⟨n, by omega⟩

theorem cmp_le_two (P R : ℕ × ℕ × ℕ) : Window.cmp P R ≤ 2 := by
  unfold Window.cmp
  split_ifs <;> norm_num

/-- The constant comparison weight across two intervals is at most `2`. -/
theorem cmpConst_iff_fin (p q : Fin I.length) :
    (∃ k : ℕ, ∀ i j : Fin n, I.index i = p → I.index j = q →
        Window.cmp (Window.triple a b (Window.complement N c) i)
          (Window.triple a b (Window.complement N c) j) = k) ↔
      ∃ k : Fin 3, ∀ i j : Fin n, I.index i = p → I.index j = q →
        Window.cmp (Window.triple a b (Window.complement N c) i)
          (Window.triple a b (Window.complement N c) j) = (k : ℕ) := by
  constructor
  · rintro ⟨k, hk⟩
    have h := hk (I.first p) (I.first q) (I.index_embedding _ _) (I.index_embedding _ _)
    have h2 := cmp_le_two (Window.triple a b (Window.complement N c) (I.first p))
      (Window.triple a b (Window.complement N c) (I.first q))
    exact ⟨⟨k, by omega⟩, hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, hk⟩

/-- Definition 5.1 for a given partition, with every quantifier bounded. -/
def IsQuiverPartitionFin : Prop :=
  (∑ i, a i + ∑ i, b i = ∑ i, c i) ∧ (∀ i, c i ≤ N) ∧
    (∀ k : Fin (n + 1), 0 ≤ Window.prefixHeight a b c k.val) ∧
    WindowInequalityFin a b c a ∧ WindowInequalityFin a b c b ∧
    WindowInequalityFin a b c (Window.complement N c) ∧
    (∀ i j : Fin n, i ≤ j → I.index i = I.index j →
      a j ≤ a i ∧ b j ≤ b i ∧ Window.complement N c j ≤ Window.complement N c i) ∧
    (∀ p q : Fin I.length, p < q → ∃ k : Fin 3, ∀ i j : Fin n, I.index i = p → I.index j = q →
      Window.cmp (Window.triple a b (Window.complement N c) i)
        (Window.triple a b (Window.complement N c) j) = (k : ℕ))

instance (u : Composition n) : Decidable (WindowInequalityFin a b c u) := by
  unfold WindowInequalityFin
  infer_instance

instance : Decidable (IsQuiverPartitionFin a b c N I) := by
  unfold IsQuiverPartitionFin
  infer_instance

theorem isQuiverPartition_iff_fin :
    IsQuiverPartition a b c N I ↔ IsQuiverPartitionFin a b c N I := by
  constructor
  · intro h
    exact ⟨h.hyp.balance, h.hyp.le_N, (heightNonneg_iff_fin a b c).1 h.hyp.height_nonneg,
      (windowInequality_iff_fin a b c a).1 h.hyp.window_a,
      (windowInequality_iff_fin a b c b).1 h.hyp.window_b,
      (windowInequality_iff_fin a b c _).1 h.hyp.window_c, h.antitone,
      fun p q hpq => (cmpConst_iff_fin a b c N I p q).1 (h.cmp_const p q hpq)⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨⟨h1, h2, (heightNonneg_iff_fin a b c).2 h3, (windowInequality_iff_fin a b c a).2 h4,
      (windowInequality_iff_fin a b c b).2 h5, (windowInequality_iff_fin a b c _).2 h6⟩, h7,
      fun p q hpq => (cmpConst_iff_fin a b c N I p q).2 (h8 p q hpq)⟩

instance instDecidableIsQuiverPartition : Decidable (IsQuiverPartition a b c N I) :=
  decidable_of_iff _ (isQuiverPartition_iff_fin a b c N I).symm

/-- **Being a quiver triple is decidable**, by checking the canonical partition. -/
instance instDecidableIsQuiverTriple : Decidable (IsQuiverTriple a b c) :=
  decidable_of_iff _ isQuiverTriple_iff_canonical.symm

end Decidable

end Schubert.RS.Quiver
