import Schubert.RS.Hall.Reduction
import Schubert.RS.Family.RootWindow

/-!
# The 2-Hall partition of the counterexample family

The triples `(a, b, c)` of Theorem 1.1 are Hall triples (Definition 3.9): the partition of the
positions by coordinate class is a `2`-Hall partition (`Schubert.RS.Family.familyHallPartition`),
with

* the distinguished blocks `B_1 = {i : a_i = 0}` and `B_2 = {i : b_i = 0}`
  (`Schubert.RS.Family.mem_familyDist_zero`, `Schubert.RS.Family.mem_familyDist_one`);
* the other blocks the pairs of target positions of equal class, `{m + k − 1, 4m + 1 − k}` for
  `2 ≤ k ≤ m + 1` in `0`-based positions (`Schubert.RS.Family.mem_familyBlock_target`), that is,
  the pairs `{q_j, q_{2m+1−j}}` of the paper.

Its conditions are the family's residual pattern (`Schubert.RS.Family.residual_pattern`), the
comparison pattern (`Schubert.RS.Family.class_pattern`), the prefix heights
`Schubert.RS.Family.beta` and the ascent gaps of `Family/WindowData.lean`, with `N` the rectangle
`(m + 3)K − 1`. Proposition 3.11 (`Schubert.RS.Hall.paired_reduction`) then applies to the family
(`Schubert.RS.Family.atomCoefficient_eq_paired`). The value of the family coefficient is proved
separately, in `Family/Main.lean`.

## Main definitions

* `Schubert.RS.Family.familyHallPartition`

## Main results

* `Schubert.RS.Family.isHallTriple_family`
* `Schubert.RS.Family.sameBlock_family_iff`
* `Schubert.RS.Family.atomCoefficient_eq_paired`
-/

namespace Schubert.RS.Family

open Finset Window

variable (P : Parameters)

/-! ### Window data -/

theorem prefixHeight_family {k : ℕ} (hk : k ≤ P.rank) :
    prefixHeight (a P) (b P) (c P) k = (beta P ⟨k, by omega⟩ : ℤ) :=
  beta_is_prefix P ⟨k, by omega⟩

theorem prefixHeight_family_of_le {k : ℕ} (hk : P.rank ≤ k) :
    prefixHeight (a P) (b P) (c P) k = 0 := by
  have h : prefixHeight (a P) (b P) (c P) k = prefixHeight (a P) (b P) (c P) P.rank := by
    unfold prefixHeight
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and]
    have := i.isLt
    omega
  rw [h, prefixHeight_family P le_rfl]
  have := beta_finish P
  simp only [Fin.last] at this
  rw [this, Nat.cast_zero]

/-- The family satisfies the hypotheses of Proposition 2.13 with `N` the rectangle. -/
theorem hypotheses_family : Hypotheses (a P) (b P) (c P) P.rectangle where
  balance := by
    have h := prefixHeight_family_of_le P (le_refl P.rank)
    unfold prefixHeight at h
    rw [Finset.filter_true_of_mem fun i _ => i.isLt] at h
    simp only [residual, Finset.sum_sub_distrib] at h
    have : (∑ i, (c P i : ℤ)) = ∑ i, (a P i : ℤ) + ∑ i, (b P i : ℤ) := by linarith
    exact_mod_cast this.symm
  le_N := c_le P
  height_nonneg k := by
    rcases le_total k P.rank with hk | hk
    · rw [prefixHeight_family P hk]
      exact Nat.cast_nonneg _
    · rw [prefixHeight_family_of_le P hk]
  window_a i j hij h := by
    refine ⟨i.val, le_rfl, hij, ?_⟩
    have hj := j.isLt
    rw [prefixHeight_family P (by omega)]
    have h1 := beta_bound P ⟨i.val + 1, by omega⟩
    have h2 := ascent_gap_a P i j h
    omega
  window_b i j hij h := by
    refine ⟨i.val, le_rfl, hij, ?_⟩
    have hj := j.isLt
    rw [prefixHeight_family P (by omega)]
    have h1 := beta_bound P ⟨i.val + 1, by omega⟩
    have h2 := ascent_gap_b P i j h
    omega
  window_c i j hij h := by
    refine ⟨i.val, le_rfl, hij, ?_⟩
    have hj := j.isLt
    rw [prefixHeight_family P (by omega)]
    have h1 := beta_bound P ⟨i.val + 1, by omega⟩
    have h2 := ascent_gap_g P i j h
    change (beta P ⟨i.val + 1, _⟩ : ℤ) < (g P j : ℤ) - g P i + 1
    omega

/-! ### The blocks -/

instance : DecidableRel (Setoid.ker (coordinateClass P)).r := fun i j =>
  inferInstanceAs (Decidable (coordinateClass P i = coordinateClass P j))

/-- The partition of the positions by coordinate class. -/
def familyBlocks : Finpartition (Finset.univ : Finset (Fin P.rank)) :=
  Finpartition.ofSetoid (Setoid.ker (coordinateClass P))

theorem mem_familyBlocks {B : Finset (Fin P.rank)} :
    B ∈ (familyBlocks P).parts ↔
      ∃ i, (Finset.univ.filter fun j => coordinateClass P i = coordinateClass P j) = B := by
  change B ∈ Finset.univ.image (fun i => Finset.univ.filter
    fun j => coordinateClass P i = coordinateClass P j) ↔ _
  simp

/-- **Two positions lie in the same block exactly when they have the same coordinate class.** -/
theorem sameBlock_family_iff (i j : Fin P.rank) :
    (∃ B ∈ (familyBlocks P).parts, i ∈ B ∧ j ∈ B) ↔ coordinateClass P i = coordinateClass P j := by
  constructor
  · rintro ⟨B, hB, hi, hj⟩
    obtain ⟨k, rfl⟩ := (mem_familyBlocks P).mp hB
    simp only [mem_filter, mem_univ, true_and] at hi hj
    exact hi.symm.trans hj
  · intro h
    refine ⟨_, (mem_familyBlocks P).mpr ⟨i, rfl⟩, ?_, ?_⟩ <;>
      simp only [mem_filter, mem_univ, true_and, h]

/-- The distinguished blocks: the positions of class `0` and of class `1`. -/
def familyDist (s : Fin 2) : Finset (Fin P.rank) :=
  Finset.univ.filter fun j => (coordinateClass P j : ℕ) = s

theorem mem_familyDist {s : Fin 2} {i : Fin P.rank} :
    i ∈ familyDist P s ↔ (coordinateClass P i : ℕ) = s := by
  simp [familyDist]

theorem exists_mem_familyDist_iff (i : Fin P.rank) :
    (∃ s, i ∈ familyDist P s) ↔ sourceClass P i := by
  simp only [mem_familyDist, sourceClass]
  constructor
  · rintro ⟨s, hs⟩
    rw [hs]
    exact s.isLt
  · intro h
    exact ⟨⟨_, h⟩, rfl⟩

theorem exists_class_lt_two {k : ℕ} (hk : k < 2) : ∃ i, (coordinateClass P i : ℕ) = k := by
  have hm := P.m_pos
  have hp := P.p_pos
  have hq := P.q_pos
  have hpq := P.pq_eq
  have hpm := P.p_le_m
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · exact ⟨⟨0, by unfold Parameters.rank; omega⟩, early_source_A P _ hp⟩
  · exact ⟨⟨P.p, by unfold Parameters.rank; omega⟩, early_source_B P _ le_rfl (by simp; omega)⟩

theorem familyDist_mem (s : Fin 2) : familyDist P s ∈ (familyBlocks P).parts := by
  obtain ⟨i, hi⟩ := exists_class_lt_two P s.isLt
  refine (mem_familyBlocks P).mpr ⟨i, ?_⟩
  ext j
  simp only [familyDist, mem_filter, mem_univ, true_and, Fin.ext_iff, hi]
  exact eq_comm

/-- `B_1` is the set of positions with `a_i = 0`. -/
theorem mem_familyDist_zero (i : Fin P.rank) : i ∈ familyDist P 0 ↔ a P i = 0 := by
  rw [mem_familyDist]
  simp only [a, Fin.val_zero, Nat.mul_eq_zero, P.K_pos.ne', or_false]

/-- `B_2` is the set of positions with `b_i = 0`. -/
theorem mem_familyDist_one (i : Fin P.rank) : i ∈ familyDist P 1 ↔ b P i = 0 := by
  rw [mem_familyDist]
  have hc := (coordinateClass P i).isLt
  simp only [b, Fin.val_one, Nat.mul_eq_zero, P.K_pos.ne', or_false]
  split_ifs with h0 h1 <;> constructor <;> intro h <;> first | omega | exact h.elim

/-- The block of a target position of class `k ≥ 2` is the pair `{m + k − 1, 4m + 1 − k}`. -/
theorem mem_familyBlock_target {i j : Fin P.rank} (hi : 2 ≤ (coordinateClass P i : ℕ)) :
    coordinateClass P j = coordinateClass P i ↔
      j.val = P.m + (coordinateClass P i : ℕ) - 1 ∨
        j.val = 4 * P.m + 1 - (coordinateClass P i : ℕ) := by
  have hc := (coordinateClass P i).isLt
  have hj := j.isLt
  change j.val < 4 * P.m at hj
  have hp := P.p_pos
  have hpm := P.p_le_m
  rw [Fin.ext_iff]
  generalize (coordinateClass P i : ℕ) = k at hi hc ⊢
  constructor
  · intro h
    unfold coordinateClass at h
    simp only at h
    split_ifs at h <;> omega
  · rintro (h | h)
    · rw [early_target P j (by omega) (by omega)]
      omega
    · rw [late_target P j (by omega)]
      omega

theorem familyBlocks_card_le_two (B : Finset (Fin P.rank)) (hB : B ∈ (familyBlocks P).parts)
    (hnd : ∀ s, B ≠ familyDist P s) : B.card ≤ 2 := by
  obtain ⟨i, rfl⟩ := (mem_familyBlocks P).mp hB
  have hi : 2 ≤ (coordinateClass P i : ℕ) := by
    by_contra h
    refine hnd ⟨(coordinateClass P i : ℕ), by omega⟩ ?_
    ext j
    simp only [familyDist, mem_filter, mem_univ, true_and, Fin.ext_iff]
    exact eq_comm
  have hc := (coordinateClass P i).isLt
  have hm := P.m_pos
  have hsub : (Finset.univ.filter fun j => coordinateClass P i = coordinateClass P j) ⊆
      {⟨P.m + (coordinateClass P i : ℕ) - 1, by unfold Parameters.rank; omega⟩,
        ⟨4 * P.m + 1 - (coordinateClass P i : ℕ), by unfold Parameters.rank; omega⟩} := by
    intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj
    rcases (mem_familyBlock_target P hi).mp hj.symm with h | h
    · exact mem_insert.mpr (Or.inl (Fin.ext h))
    · exact mem_insert.mpr (Or.inr (mem_singleton.mpr (Fin.ext h)))
  exact (card_le_card hsub).trans card_le_two

/-! ### The Hall partition -/

/-- **The `2`-Hall partition of the family** (Definition 3.9), with `N = (m + 3)K − 1`: the
positions partitioned by coordinate class, with distinguished blocks the positions of class `0`
(`a_i = 0`) and of class `1` (`b_i = 0`). -/
def familyHallPartition : Hall.HallPartition (a P) (b P) (c P) P.rectangle 2 where
  blocks := familyBlocks P
  dist := familyDist P
  dist_mem := familyDist_mem P
  dist_injective := by
    intro s t h
    obtain ⟨i, hi⟩ := exists_class_lt_two P s.isLt
    have h1 : i ∈ familyDist P s := (mem_familyDist P).mpr hi
    rw [h, mem_familyDist] at h1
    exact Fin.ext (hi.symm.trans h1)
  card_le_two := familyBlocks_card_le_two P
  residual_eq i := by
    rw [residual, residual_pattern]
    exact if_congr (exists_mem_familyDist_iff P i).symm rfl rfl
  cmp_eq i j _ := by
    change comparisonWeight P i j = _
    rw [class_pattern]
    exact if_congr (sameBlock_family_iff P i j).symm rfl
      (if_congr (and_congr (exists_mem_familyDist_iff P i).symm
        (not_congr (exists_mem_familyDist_iff P j).symm)) rfl rfl)
  hypotheses := hypotheses_family P

/-- **The triples of Theorem 1.1 are Hall triples.** -/
theorem isHallTriple_family : Hall.IsHallTriple (a P) (b P) (c P) := by
  have hm := P.m_pos
  exact ⟨P.rectangle, 2, by omega, by unfold Parameters.rank; omega, ⟨familyHallPartition P⟩⟩

/-- **Proposition 3.11 for the family**: the atom coefficient of the family is the coefficient of
`t_1 ⋯ t_m` in the product of the Hall polynomials of `B_1`, `B_2` and the pair factors of its
`2`-Hall partition. -/
theorem atomCoefficient_eq_paired :
    atomCoefficient (key (a P) * key (b P)) (c P) =
      ((∏ s, (familyHallPartition P).blockPolynomial s Hall.tVar) *
        ∏ ij ∈ (familyHallPartition P).pairs,
          (1 - AddMonoidAlgebra.single (Pi.single ij.2 1 - Pi.single ij.1 1) 1 :
            Laurent (familyHallPartition P).m)).coeff (fun _ => 1) :=
  Hall.paired_reduction (familyHallPartition P)

end Schubert.RS.Family
