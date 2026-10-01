import Schubert.RS.Hall.Admissible
import Schubert.RS.Window.General
import Mathlib.Order.Partition.Finpartition

/-!
# Hall partitions and Hall triples

Definition 3.9 of the paper (`def:paired-target`). Let `a, b, c` be weak compositions of length `n`
with `|a| + |b| = |c|`, choose `N ≥ max c` and put `c̄ = N·1 − c`. An *`r`-Hall partition* for
`(a, b, c)` is a partition `𝓑` of the positions, with `r` distinguished blocks `B_1, …, B_r`, such
that every other block has one or two elements and

1. `c_i − a_i − b_i` is `1` on `B_1 ∪ ⋯ ∪ B_r` and `−1` elsewhere;
2. for `i < j`, `cmp((a_i,b_i,c̄_i),(a_j,b_j,c̄_j))` is `−1` if `i` and `j` lie in the same block,
   `1` if `i` is distinguished and `j` is not, and `0` otherwise;
3. the prefix heights are nonnegative and the window inequalities hold for `a`, `b`, `c̄`.

`(a, b, c)` is a *Hall triple* if it admits an `r`-Hall partition for some `1 ≤ r ≤ n`. The
definition does not depend on `N` (`HallPartition.changeN`, `isHallTriple_iff`).

The notation used in Proposition 3.11 (`prop:paired-reduction`) is attached to a Hall partition:
the non-distinguished positions `q_1 < ⋯ < q_m`, the pairs `𝓔`, the heights `ℓ_{s,j}`, the flags
`f_{s,k}` and the Hall polynomials `P_s(t_1, …, t_m)` of (3.10) (eq:hall-polynomial). Positions are
`0`-based in Lean.

## Main definitions

* `Schubert.RS.Hall.HallPartition a b c N r`: an `r`-Hall partition for `(a, b, c)`.
* `Schubert.RS.Hall.IsHallTriple a b c`.
* `Schubert.RS.Hall.HallPartition.blockPolynomial`: the Hall polynomial `P_s` of the block `B_s`.

## Main results

* `Schubert.RS.Hall.isHallTriple_iff`: independence of `N`.
* `Schubert.RS.Hall.HallPartition.m_eq_sum_card`: `m = ∑_s |B_s|`.
* `Schubert.RS.Hall.HallPartition.blockPolynomial_eq_hallAdmissible`: by Lemma 3.8, `P_s` is the
  sum over the Hall-admissible subsets for `ℓ_{s,1}, …, ℓ_{s,m}`.
-/

namespace Schubert.RS.Hall

open Window

variable {n : ℕ}

/-- An **`r`-Hall partition** for `(a, b, c)` with `c̄ = N·1 − c` (Definition 3.9 of the paper,
`def:paired-target`): a partition `blocks` of the positions with `r` distinguished blocks
`dist 0, …, dist (r − 1)`, every other block of size at most two, satisfying conditions (i)–(iii).
The degree equality `|a| + |b| = |c|` and the bound `N ≥ max c` of the preamble are part of
`hypotheses`, together with condition (iii). -/
structure HallPartition (a b c : Composition n) (N r : ℕ) where
  /-- The partition `𝓑` of `{0, …, n − 1}`. -/
  blocks : Finpartition (Finset.univ : Finset (Fin n))
  /-- The distinguished blocks `B_1, …, B_r`. -/
  dist : Fin r → Finset (Fin n)
  dist_mem : ∀ s, dist s ∈ blocks.parts
  dist_injective : Function.Injective dist
  /-- Every block other than the distinguished ones has one or two elements. -/
  card_le_two : ∀ B ∈ blocks.parts, (∀ s, B ≠ dist s) → B.card ≤ 2
  /-- Condition (i). -/
  residual_eq : ∀ i, residual a b c i = if ∃ s, i ∈ dist s then 1 else -1
  /-- Condition (ii). -/
  cmp_eq : ∀ i j : Fin n, i < j →
    cmp (triple a b (complement N c) i) (triple a b (complement N c) j) =
      if ∃ B ∈ blocks.parts, i ∈ B ∧ j ∈ B then -1
      else if (∃ s, i ∈ dist s) ∧ ¬ ∃ s, j ∈ dist s then 1 else 0
  /-- `|a| + |b| = |c|`, `N ≥ max c`, and condition (iii). -/
  hypotheses : Hypotheses a b c N

/-- `(a, b, c)` is a **Hall triple** if, for some `N ≥ max c`, it admits an `r`-Hall partition for
some `1 ≤ r ≤ n`. By `isHallTriple_iff` the choice of `N` does not matter. -/
def IsHallTriple (a b c : Composition n) : Prop :=
  ∃ N r : ℕ, 1 ≤ r ∧ r ≤ n ∧ Nonempty (HallPartition a b c N r)

namespace HallPartition

variable {a b c : Composition n} {N r : ℕ}

/-- Changing `N ≥ max c` preserves Hall partitions (the remark after Definition 3.9). -/
def changeN (P : HallPartition a b c N r) {N' : ℕ} (hN' : ∀ i, c i ≤ N') :
    HallPartition a b c N' r where
  blocks := P.blocks
  dist := P.dist
  dist_mem := P.dist_mem
  dist_injective := P.dist_injective
  card_le_two := P.card_le_two
  residual_eq := P.residual_eq
  cmp_eq := fun i j hij => by
    rw [← cmp_complement_eq a b P.hypotheses.le_N hN' i j]
    exact P.cmp_eq i j hij
  hypotheses := (hypotheses_iff_of_le P.hypotheses.le_N hN').mp P.hypotheses

end HallPartition

/-- The definition of a Hall triple is independent of the choice of `N ≥ max c`. -/
theorem isHallTriple_iff {a b c : Composition n} {N : ℕ} (hN : ∀ i, c i ≤ N) :
    IsHallTriple a b c ↔ ∃ r : ℕ, 1 ≤ r ∧ r ≤ n ∧ Nonempty (HallPartition a b c N r) := by
  constructor
  · rintro ⟨N', r, hr, hrn, ⟨P⟩⟩
    exact ⟨r, hr, hrn, ⟨P.changeN hN⟩⟩
  · rintro ⟨r, hr, hrn, hP⟩
    exact ⟨N, r, hr, hrn, hP⟩

namespace HallPartition

variable {a b c : Composition n} {N r : ℕ} (P : HallPartition a b c N r)

/-! ### The notation of Proposition 3.11 -/

/-- The union `B_1 ∪ ⋯ ∪ B_r` of the distinguished blocks. -/
def distinguished : Finset (Fin n) := Finset.univ.biUnion P.dist

theorem mem_distinguished {i : Fin n} : i ∈ P.distinguished ↔ ∃ s, i ∈ P.dist s := by
  simp [distinguished]

/-- The number `m` of non-distinguished positions. -/
def m : ℕ := P.distinguishedᶜ.card

/-- The non-distinguished positions `q_1 < ⋯ < q_m`. -/
def q : Fin P.m ↪o Fin n :=
  P.distinguishedᶜ.orderEmbOfFin (show P.distinguishedᶜ.card = P.m from rfl)

theorem q_not_mem (j : Fin P.m) : P.q j ∉ P.distinguished :=
  Finset.mem_compl.mp (Finset.orderEmbOfFin_mem _ _ j)

theorem exists_q {i : Fin n} (hi : i ∉ P.distinguished) : ∃ j, P.q j = i := by
  have h := Finset.range_orderEmbOfFin P.distinguishedᶜ (show P.distinguishedᶜ.card = P.m from rfl)
  have : i ∈ Set.range P.q := by
    change i ∈ Set.range
      (P.distinguishedᶜ.orderEmbOfFin (show P.distinguishedᶜ.card = P.m from rfl))
    rw [h]
    simpa using hi
  exact this

/-- The pairs `𝓔`: `(i, j)` with `i < j` such that `{q_i, q_j}` is a two-element block of `𝓑`
that is not distinguished. -/
def pairs : Finset (Fin P.m × Fin P.m) :=
  Finset.univ.filter fun ij => ij.1 < ij.2 ∧
    ({P.q ij.1, P.q ij.2} : Finset (Fin n)) ∈ P.blocks.parts ∧
    ∀ s, ({P.q ij.1, P.q ij.2} : Finset (Fin n)) ≠ P.dist s

/-- The heights `ℓ_{s,j} = #{i ∈ B_s : i < q_j}`. -/
def height (s : Fin r) (j : Fin P.m) : ℕ := ((P.dist s).filter (· < P.q j)).card

theorem height_monotone (s : Fin r) : Monotone (P.height s) := by
  intro j j' hjj'
  refine Finset.card_le_card fun i hi => ?_
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, hi.2.trans_le (P.q.monotone hjj')⟩

/-- The flags `f_{s,k}` obtained from `ℓ_{s,1}, …, ℓ_{s,m}` by (3.7) (eq:canonical-flags). -/
noncomputable def flag (s : Fin r) (k : ℕ) : ℕ := hallFlag (P.height s) k

/-- **The Hall polynomial associated with `B_s`** ((3.10), eq:hall-polynomial):
`P_s(t) = ∑ t_{j_1} ⋯ t_{j_d}` over `1 ≤ j_1 < ⋯ < j_d ≤ m` with `j_k ≥ f_{s,k}`, where `d = |B_s|`.
In Lean `j_k = J (k − 1) + 1`. -/
noncomputable def blockPolynomial {R : Type*} [CommRing R] (s : Fin r) (t : Fin P.m → R) : R :=
  ∑ J ∈ Finset.univ.filter (fun J : Fin (P.dist s).card → Fin P.m =>
      StrictMono J ∧ ∀ k : Fin (P.dist s).card, P.flag s (k.val + 1) ≤ (J k).val + 1),
    ∏ k, t (J k)

/-- By Lemma 3.8, `P_s` is the sum over the Hall-admissible subsets for `ℓ_{s,1}, …, ℓ_{s,m}`. -/
theorem blockPolynomial_eq_hallAdmissible {R : Type*} [CommRing R] (s : Fin r)
    (t : Fin P.m → R) :
    P.blockPolynomial s t =
      ∑ J ∈ Finset.univ.filter (IsHallAdmissible (d := (P.dist s).card) (P.height s)),
        ∏ k, t (J k) := by
  unfold blockPolynomial flag
  congr 1
  ext J
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (isHallAdmissible_iff_flags (P.height s) (P.height_monotone s) J).symm

/-! ### Basic properties -/

theorem dist_disjoint {s s' : Fin r} (h : s ≠ s') : Disjoint (P.dist s) (P.dist s') :=
  P.blocks.disjoint (P.dist_mem s) (P.dist_mem s') (fun he => h (P.dist_injective he))

theorem dist_pairwiseDisjoint :
    ((Finset.univ : Finset (Fin r)) : Set (Fin r)).PairwiseDisjoint P.dist :=
  fun _ _ _ _ h => P.dist_disjoint h

theorem card_distinguished : P.distinguished.card = ∑ s, (P.dist s).card :=
  Finset.card_biUnion fun _ _ _ _ h => P.dist_disjoint h

/-- Since `∑_i (c_i − a_i − b_i) = 0`, condition (i) gives `m = ∑_s |B_s|`. -/
theorem m_eq_sum_card : P.m = ∑ s, (P.dist s).card := by
  classical
  rw [← card_distinguished]
  have h0 := sum_residual_eq_zero P.hypotheses.balance
  have hsplit := Finset.sum_add_sum_compl P.distinguished (residual a b c)
  have h1 : ∑ i ∈ P.distinguished, residual a b c i = P.distinguished.card := by
    rw [Finset.sum_congr rfl fun i hi => by
      rw [P.residual_eq, ite_eq_left ((P.mem_distinguished).mp hi)]]
    simp
  have h2 : ∑ i ∈ P.distinguishedᶜ, residual a b c i = -(P.distinguishedᶜ.card : ℤ) := by
    rw [Finset.sum_congr rfl fun i hi => by
      rw [P.residual_eq,
        ite_eq_right (fun h => Finset.mem_compl.mp hi ((P.mem_distinguished).mpr h))]]
    simp
  unfold m
  omega

/-- The block containing a distinguished position is its distinguished block. -/
theorem sameBlock_iff_of_mem_dist {s : Fin r} {i : Fin n} (hi : i ∈ P.dist s) (j : Fin n) :
    (∃ B ∈ P.blocks.parts, i ∈ B ∧ j ∈ B) ↔ j ∈ P.dist s := by
  constructor
  · rintro ⟨B, hB, hiB, hjB⟩
    rwa [P.blocks.eq_of_mem_parts hB (P.dist_mem s) hiB hi] at hjB
  · intro hj
    exact ⟨P.dist s, P.dist_mem s, hi, hj⟩

/-- Two distinct non-distinguished positions lie in the same block exactly when they form a
two-element non-distinguished block. -/
theorem sameBlock_iff_of_not_mem {i j : Fin n} (hi : i ∉ P.distinguished) (hij : i ≠ j) :
    (∃ B ∈ P.blocks.parts, i ∈ B ∧ j ∈ B) ↔
      ({i, j} : Finset (Fin n)) ∈ P.blocks.parts ∧ ∀ s, ({i, j} : Finset (Fin n)) ≠ P.dist s := by
  constructor
  · rintro ⟨B, hB, hiB, hjB⟩
    have hnd : ∀ s, B ≠ P.dist s := fun s he =>
      hi ((P.mem_distinguished).mpr ⟨s, he ▸ hiB⟩)
    have hsub : ({i, j} : Finset (Fin n)) ⊆ B := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hiB
      · rw [Finset.mem_singleton.mp hx]
        exact hjB
    have hcard : B.card ≤ ({i, j} : Finset (Fin n)).card := by
      rw [Finset.card_pair hij]
      exact P.card_le_two B hB hnd
    have he := Finset.eq_of_subset_of_card_le hsub hcard
    rw [he]
    exact ⟨hB, hnd⟩
  · rintro ⟨hB, -⟩
    exact ⟨_, hB, by simp, by simp⟩

end HallPartition

end Schubert.RS.Hall
