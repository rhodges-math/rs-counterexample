import RSCounterexample.Paper.Complexity.Encoding

/-!
# Quiver triples in arithmetic form

The recognition algorithm checks Definition 5.1 on the canonical partition (the paper's
recognition argument, lines 1879–1893), using only comparisons of sums of input entries. This file
rewrites `IsQuiverTripleList a b c` in that form (`isQuiverTripleList_iff_listConditions`):

* the degree equality and the nonnegativity of the prefix heights compare prefix sums;
* each window inequality `h_{k+1} < u_j − u_i + 1` becomes
  `C_{k+1} + u_i < A_{k+1} + B_{k+1} + u_j + 1` for prefix sums `A`, `B`, `C` (and with the roles
  of `c_i`, `c_j` exchanged for `u = c̄`);
* two positions lie in the same interval of the canonical partition exactly when the triple does
  not rise between them (`SameBlock`), and condition (i) holds automatically;
* condition (ii) compares the counts `cmp + 1` of strict increases (`cmpCount`).
-/

namespace Schubert.RS.Algorithms

open Quiver

/-- The prefix sum `x_0 + ⋯ + x_{k−1}`; entries beyond the list are `0`. -/
def psum (x : List ℕ) (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, x.getD i 0

/-- From position `m` to `m + 1`, `a` or `b` strictly increases or `c` strictly decreases. -/
def RisesAt (a b c : List ℕ) (m : ℕ) : Prop :=
  a.getD m 0 < a.getD (m + 1) 0 ∨ b.getD m 0 < b.getD (m + 1) 0 ∨ c.getD (m + 1) 0 < c.getD m 0

/-- The triple does not rise between positions `i` and `j`: they lie in the same interval of the
canonical partition. -/
def SameBlock (a b c : List ℕ) (i j : ℕ) : Prop :=
  ∀ m < c.length, min i j ≤ m → m < max i j → ¬ RisesAt a b c m

/-- The number `cmp + 1` of strict increases from `(a_i, b_i, c̄_i)` to `(a_j, b_j, c̄_j)`. -/
def cmpCount (a b c : List ℕ) (i j : ℕ) : ℕ :=
  (if a.getD i 0 < a.getD j 0 then 1 else 0) + (if b.getD i 0 < b.getD j 0 then 1 else 0) +
    (if c.getD j 0 < c.getD i 0 then 1 else 0)

/-- The window inequality (2.12) for `u = a` or `u = b`, in terms of prefix sums. -/
def WindowOK (a b c u : List ℕ) : Prop :=
  ∀ i < c.length, ∀ j < c.length, i < j → u.getD i 0 < u.getD j 0 →
    ∃ k < c.length, i ≤ k ∧ k < j ∧
      psum c (k + 1) + u.getD i 0 < psum a (k + 1) + psum b (k + 1) + u.getD j 0 + 1

/-- The window inequality (2.12) for `c̄ = N·1 − c`, in terms of prefix sums. -/
def WindowOKc (a b c : List ℕ) : Prop :=
  ∀ i < c.length, ∀ j < c.length, i < j → c.getD j 0 < c.getD i 0 →
    ∃ k < c.length, i ≤ k ∧ k < j ∧
      psum c (k + 1) + c.getD j 0 < psum a (k + 1) + psum b (k + 1) + c.getD i 0 + 1

/-- Definition 5.1 for lists, checked on the canonical partition with comparisons of sums. -/
structure ListConditions (a b c : List ℕ) : Prop where
  len_a : a.length = c.length
  len_b : b.length = c.length
  balance : psum a c.length + psum b c.length = psum c c.length
  height : ∀ k < c.length + 1, psum a k + psum b k ≤ psum c k
  window_a : WindowOK a b c a
  window_b : WindowOK a b c b
  window_c : WindowOKc a b c
  cmp : ∀ i < c.length, ∀ j < c.length, ∀ i' < c.length, ∀ j' < c.length, i < j →
    ¬ SameBlock a b c i j → SameBlock a b c i i' → SameBlock a b c j j' →
      cmpCount a b c i j = cmpCount a b c i' j' ∧ 1 ≤ cmpCount a b c i j

section Translation

variable (a b c : List ℕ) {n : ℕ}

theorem sum_toComposition (x : List ℕ) : ∑ i : Fin n, toComposition n x i = psum x n :=
  Fin.sum_univ_eq_sum_range (fun i => x.getD i 0) n

theorem prefixHeight_toComposition {k : ℕ} (hk : k ≤ n) :
    Window.prefixHeight (toComposition n a) (toComposition n b) (toComposition n c) k =
      (psum c k : ℤ) - psum a k - psum b k := by
  unfold Window.prefixHeight Window.residual
  rw [Finset.sum_filter]
  have h := Fin.sum_univ_eq_sum_range
    (fun i => if i < k then ((c.getD i 0 : ℤ) - a.getD i 0 - b.getD i 0) else 0) n
  simp only [toComposition]
  rw [h, ← Finset.sum_filter]
  have hr : (Finset.range n).filter (· < k) = Finset.range k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hr]
  simp only [psum, Finset.sum_sub_distrib, Nat.cast_sum]

/-- The canonical partition cuts between `m` and `m + 1` exactly at the rises. -/
theorem canonical_index_succ_iff {m : ℕ} (h : m + 1 < n) :
    (canonicalPartition (toComposition n a) (toComposition n b) (toComposition n c)).index
        ⟨m, by omega⟩ =
      (canonicalPartition (toComposition n a) (toComposition n b) (toComposition n c)).index
        ⟨m + 1, h⟩ ↔ ¬ RisesAt a b c m := by
  have hb := IntervalPartition.succ_mem_boundaries_iff
    (canonicalPartition (toComposition n a) (toComposition n b) (toComposition n c))
    ⟨m, by omega⟩ h
  have hbd : (canonicalPartition (toComposition n a) (toComposition n b)
      (toComposition n c)).boundaries =
      canonicalBoundaries (toComposition n a) (toComposition n b) (toComposition n c) :=
    CompositionAsSet.toComposition_boundaries _
  rw [hbd] at hb
  have hb' : (⟨m + 1, by omega⟩ : Fin (n + 1)) ∈
      canonicalBoundaries (toComposition n a) (toComposition n b) (toComposition n c) ↔
      (canonicalPartition (toComposition n a) (toComposition n b) (toComposition n c)).index
        ⟨m, by omega⟩ ≠
      (canonicalPartition (toComposition n a) (toComposition n b) (toComposition n c)).index
        ⟨m + 1, h⟩ := hb
  have key : (⟨m + 1, by omega⟩ : Fin (n + 1)) ∈
      canonicalBoundaries (toComposition n a) (toComposition n b) (toComposition n c) ↔
      RisesAt a b c m := by
    simp only [canonicalBoundaries, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (h0 | hn | ⟨i, hi, hie, hr⟩)
      · omega
      · omega
      · obtain ⟨iv, hiv⟩ := i
        simp only at hie
        obtain rfl : iv = m := by omega
        exact hr
    · intro hr
      exact Or.inr (Or.inr ⟨⟨m, by omega⟩, h, rfl, hr⟩)
  rw [← key, hb', not_not]

/-- Positions `i ≤ j` lie in one interval exactly when consecutive positions between them do. -/
theorem index_eq_iff_of_le (I : IntervalPartition n) {i j : Fin n} (hij : i ≤ j) :
    I.index i = I.index j ↔ ∀ m (hm : m + 1 < n), i.val ≤ m → m < j.val →
      I.index ⟨m, by omega⟩ = I.index ⟨m + 1, hm⟩ := by
  constructor
  · intro h m hm him hmj
    have h1 := I.index_mono (show i ≤ ⟨m, by omega⟩ from Fin.le_def.mpr him)
    have h2 := I.index_mono (show (⟨m, by omega⟩ : Fin n) ≤ ⟨m + 1, hm⟩ from
      Fin.le_def.mpr (Nat.le_succ m))
    have h3 := I.index_mono (show (⟨m + 1, hm⟩ : Fin n) ≤ j from Fin.le_def.mpr hmj)
    rw [h] at h1
    exact le_antisymm h2 (h3.trans h1)
  · intro h
    obtain ⟨jv, hjv⟩ := j
    obtain ⟨iv, hiv⟩ := i
    simp only [Fin.mk_le_mk] at hij
    simp only at h
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
    clear hij
    induction d with
    | zero => rfl
    | succ d ih =>
      have h1 := ih (by omega) (fun m hm him hmj => h m hm him (by omega))
      rw [h1]
      exact h (iv + d) (by omega) (by omega) (by omega)

/-- Two positions lie in one interval of the canonical partition exactly when the triple does not
rise between them. -/
theorem canonical_index_eq_iff (hn : c.length = n) (i j : Fin n) :
    (canonicalPartition (toComposition n a) (toComposition n b) (toComposition n c)).index i =
      (canonicalPartition (toComposition n a) (toComposition n b) (toComposition n c)).index j ↔
        SameBlock a b c i j := by
  have key : ∀ i j : Fin n, i ≤ j →
      ((canonicalPartition (toComposition n a) (toComposition n b) (toComposition n c)).index i =
        (canonicalPartition (toComposition n a) (toComposition n b) (toComposition n c)).index j ↔
          SameBlock a b c i j) := by
    intro i j hij
    rw [index_eq_iff_of_le _ hij, SameBlock]
    have hmin : min (i : ℕ) j = i := min_eq_left hij
    have hmax : max (i : ℕ) j = j := max_eq_right hij
    rw [hmin, hmax]
    constructor
    · intro h m _ him hmj
      exact (canonical_index_succ_iff a b c (by omega)).1 (h m (by omega) him hmj)
    · intro h m hm him hmj
      exact (canonical_index_succ_iff a b c hm).2 (h m (by omega) him hmj)
  rcases le_total i j with hij | hji
  · exact key i j hij
  · rw [eq_comm, key j i hji, SameBlock, SameBlock, min_comm, max_comm]

/-- Inside an interval of the canonical partition, `a` and `b` weakly decrease and `c` weakly
increases. -/
theorem canonical_antitone (hn : c.length = n) {i j : Fin n} (hij : i ≤ j)
    (h : (canonicalPartition (toComposition n a) (toComposition n b) (toComposition n c)).index i =
      (canonicalPartition (toComposition n a) (toComposition n b) (toComposition n c)).index j) :
    a.getD j 0 ≤ a.getD i 0 ∧ b.getD j 0 ≤ b.getD i 0 ∧ c.getD i 0 ≤ c.getD j 0 := by
  rw [canonical_index_eq_iff a b c hn] at h
  obtain ⟨jv, hjv⟩ := j
  obtain ⟨iv, hiv⟩ := i
  simp only [Fin.mk_le_mk] at hij
  simp only [SameBlock, min_eq_left hij, max_eq_right hij] at h
  show a.getD jv 0 ≤ a.getD iv 0 ∧ b.getD jv 0 ≤ b.getD iv 0 ∧ c.getD iv 0 ≤ c.getD jv 0
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction d with
  | zero => exact ⟨le_rfl, le_rfl, le_rfl⟩
  | succ d ih =>
    obtain ⟨h1, h2, h3⟩ := ih (by omega) (fun m hm him hmj => h m hm him (by omega))
    have hr := h (iv + d) (by omega) (by omega) (by omega)
    simp only [RisesAt, not_or, not_lt] at hr
    obtain ⟨ha, hb, hc⟩ := hr
    rw [← Nat.add_assoc]
    exact ⟨ha.trans h1, hb.trans h2, h3.trans hc⟩

/-- The comparison weight is `cmpCount − 1`. -/
theorem cmp_eq_cmpCount {N : ℕ} (hN : ∀ i : Fin n, toComposition n c i ≤ N) (i j : Fin n) :
    Window.cmp (Window.triple (toComposition n a) (toComposition n b)
        (Window.complement N (toComposition n c)) i)
      (Window.triple (toComposition n a) (toComposition n b)
        (Window.complement N (toComposition n c)) j) = (cmpCount a b c i j : ℤ) - 1 := by
  have hi := hN i
  have hj := hN j
  simp only [toComposition] at hi hj
  have hc : N - c.getD i 0 < N - c.getD j 0 ↔ c.getD j 0 < c.getD i 0 := by omega
  simp only [Window.cmp, Window.triple, Window.complement, toComposition, cmpCount, hc]
  push_cast
  split_ifs <;> omega

end Translation

/-- **Quiver triples in arithmetic form.** -/
theorem isQuiverTripleList_iff_listConditions (a b c : List ℕ) :
    IsQuiverTripleList a b c ↔ ListConditions a b c := by
  have hN : ∀ i : Fin c.length, c.getD i 0 ≤ Finset.univ.sup (toComposition c.length c) :=
    fun i => le_sup (toComposition c.length c) i
  have hsame := canonical_index_eq_iff a b c rfl
  have hcmp := cmp_eq_cmpCount a b c hN
  rw [IsQuiverTripleList, isQuiverTriple_iff_canonical, isQuiverPartition_iff_fin]
  constructor
  · rintro ⟨ha, hb, h1, -, h3, h4, h5, h6, -, h8⟩
    refine ⟨ha, hb, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rwa [sum_toComposition, sum_toComposition, sum_toComposition] at h1
    · intro k hk
      have := h3 ⟨k, hk⟩
      rw [prefixHeight_toComposition a b c (show k ≤ c.length by omega)] at this
      omega
    · intro i hi j hj hij hu
      obtain ⟨k, hk1, hk2, hk3⟩ := h4 ⟨i, hi⟩ ⟨j, hj⟩ hij hu
      rw [prefixHeight_toComposition a b c (show k.val + 1 ≤ c.length by omega)] at hk3
      exact ⟨k, k.isLt, hk1, hk2, by simp only [toComposition] at hk3; omega⟩
    · intro i hi j hj hij hu
      obtain ⟨k, hk1, hk2, hk3⟩ := h5 ⟨i, hi⟩ ⟨j, hj⟩ hij hu
      rw [prefixHeight_toComposition a b c (show k.val + 1 ≤ c.length by omega)] at hk3
      exact ⟨k, k.isLt, hk1, hk2, by simp only [toComposition] at hk3; omega⟩
    · intro i hi j hj hij hu
      have hci : c.getD i 0 ≤ Finset.univ.sup (toComposition c.length c) := hN ⟨i, hi⟩
      have hcj : c.getD j 0 ≤ Finset.univ.sup (toComposition c.length c) := hN ⟨j, hj⟩
      obtain ⟨k, hk1, hk2, hk3⟩ := h6 ⟨i, hi⟩ ⟨j, hj⟩ hij
        (by simp only [Window.complement, toComposition]; omega)
      rw [prefixHeight_toComposition a b c (show k.val + 1 ≤ c.length by omega)] at hk3
      refine ⟨k, k.isLt, hk1, hk2, ?_⟩
      simp only [Window.complement, toComposition] at hk3
      omega
    · intro i hi j hj i' hi' j' hj' hij hnij hii hjj
      rw [← hsame ⟨i, hi⟩ ⟨j, hj⟩] at hnij
      rw [← hsame ⟨i, hi⟩ ⟨i', hi'⟩] at hii
      rw [← hsame ⟨j, hj⟩ ⟨j', hj'⟩] at hjj
      have hpq : (canonicalPartition (toComposition c.length a) (toComposition c.length b)
          (toComposition c.length c)).index ⟨i, hi⟩ <
          (canonicalPartition (toComposition c.length a) (toComposition c.length b)
            (toComposition c.length c)).index ⟨j, hj⟩ :=
        lt_of_le_of_ne (IntervalPartition.index_mono _ (Fin.le_def.mpr hij.le)) hnij
      obtain ⟨k, hk⟩ := h8 _ _ hpq
      have e1 := hk ⟨i, hi⟩ ⟨j, hj⟩ rfl rfl
      have e2 := hk ⟨i', hi'⟩ ⟨j', hj'⟩ hii.symm hjj.symm
      rw [hcmp] at e1 e2
      simp only at e1 e2
      omega
  · rintro ⟨ha, hb, h1, h3, h4, h5, h6, h8⟩
    refine ⟨ha, hb, ?_, fun i => hN i, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rwa [sum_toComposition, sum_toComposition, sum_toComposition]
    · intro k
      rw [prefixHeight_toComposition a b c (show k.val ≤ c.length by omega)]
      have := h3 k k.isLt
      omega
    · intro i j hij hu
      obtain ⟨k, hk, hk1, hk2, hk3⟩ := h4 i i.isLt j j.isLt hij hu
      refine ⟨⟨k, hk⟩, hk1, hk2, ?_⟩
      rw [prefixHeight_toComposition a b c (show k + 1 ≤ c.length by omega)]
      simp only [toComposition]
      omega
    · intro i j hij hu
      obtain ⟨k, hk, hk1, hk2, hk3⟩ := h5 i i.isLt j j.isLt hij hu
      refine ⟨⟨k, hk⟩, hk1, hk2, ?_⟩
      rw [prefixHeight_toComposition a b c (show k + 1 ≤ c.length by omega)]
      simp only [toComposition]
      omega
    · intro i j hij hu
      have hci := hN i
      have hcj := hN j
      simp only [Window.complement, toComposition] at hu
      obtain ⟨k, hk, hk1, hk2, hk3⟩ := h6 i i.isLt j j.isLt hij (by omega)
      refine ⟨⟨k, hk⟩, hk1, hk2, ?_⟩
      rw [prefixHeight_toComposition a b c (show k + 1 ≤ c.length by omega)]
      simp only [Window.complement, toComposition]
      omega
    · intro i j hij hb'
      obtain ⟨h1, h2, h3⟩ := canonical_antitone a b c rfl hij hb'
      refine ⟨h1, h2, ?_⟩
      have hci := hN i
      have hcj := hN j
      simp only [Window.complement, toComposition]
      omega
    · intro p q hpq
      let I := canonicalPartition (toComposition c.length a) (toComposition c.length b)
        (toComposition c.length c)
      let i0 := I.first p
      let j0 := I.first q
      have hi0 : I.index i0 = p := I.index_embedding _ _
      have hj0 : I.index j0 = q := I.index_embedding _ _
      have hlt0 : i0 < j0 := IntervalPartition.embedding_lt_embedding I hpq
        ⟨0, I.one_le_blocksFun p⟩ ⟨0, I.one_le_blocksFun q⟩
      have hne0 : ¬ SameBlock a b c i0 j0 := by
        rw [← hsame, hi0, hj0]
        exact hpq.ne
      obtain ⟨-, hpos⟩ := h8 i0 i0.isLt j0 j0.isLt i0 i0.isLt j0 j0.isLt hlt0 hne0
        ((hsame i0 i0).1 rfl) ((hsame j0 j0).1 rfl)
      have hle3 : cmpCount a b c i0 j0 ≤ 3 := by
        simp only [cmpCount]
        split_ifs <;> omega
      refine ⟨⟨cmpCount a b c i0 j0 - 1, by omega⟩, fun i j hi hj => ?_⟩
      have hij : i < j := by
        by_contra hji
        have := IntervalPartition.index_mono I (not_lt.mp hji)
        rw [hi, hj] at this
        exact absurd hpq (not_lt.mpr this)
      have hne : ¬ SameBlock a b c i j := by
        rw [← hsame, hi, hj]
        exact hpq.ne
      obtain ⟨heq, -⟩ := h8 i i.isLt j j.isLt i0 i0.isLt j0 j0.isLt hij hne
        ((hsame i i0).1 (hi.trans hi0.symm)) ((hsame j j0).1 (hj.trans hj0.symm))
      rw [hcmp]
      simp only
      omega

end Schubert.RS.Algorithms
