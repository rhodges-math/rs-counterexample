import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Finite.Perm
import Schubert.FlagVarieties.Bruhat.Order

/-!
# The Coxeter presentation of the symmetric group

`S_{n+1} = Perm (Fin (n + 1))` is the Coxeter group of type `A_n`, with simple reflections the
adjacent transpositions `s_i = (i, i + 1)`.

* `toPerm n : W(A_n) →* S_{n+1}`, `s_i ↦ (i, i + 1)`: the Coxeter relations hold
  (`isLiftable_adjSwap`), and it is surjective (adjacent transpositions generate).
* `finite_and_card_le`: `|W(A_n)| ≤ (n + 1)!`, by induction: with `H` the image of `W(A_{n-1})`,
  `W(A_n) = ⋃_{k ≤ n+1} H · c_k`, `c_k = s_n s_{n-1} ⋯ s_k` (the union is stable under right
  multiplication by every `s_j`).
* **`permCoxeterSystem n : CoxeterSystem (CoxeterMatrix.A n) (Equiv.Perm (Fin (n + 1)))`**, with
  `permCoxeterSystem_simple`: the simple reflections are the adjacent transpositions.
* **`length_eq`**: the Coxeter length is the number of inversions
  (`Schubert.FinPermutation.length`).
* **`strongBruhatLE_iff_exists_reduced_sublist`**: for a reduced word `ω` in the Coxeter system,
  `u ≤ᴮ π ω` (the rank-matrix order) iff `u` is the product of a reduced subword of `ω`. This is the
  subword description of the Bruhat order of the Coxeter system; together with Tau Ceti's subword
  property it identifies `≤ᴮ` with `CoxeterSystem.BruhatLE` (`Bruhat/CoxeterBruhat`).
-/

namespace FlagVarieties.Bruhat

open Schubert Schubert.FinPermutation

/-! ### Group lemmas -/

section GroupLemmas

variable {G : Type*} [Group G] {a b : G}

theorem pow_two_eq_one_of_commute (ha : a * a = 1) (hb : b * b = 1) (h : a * b = b * a) :
    (a * b) ^ 2 = 1 := by
  rw [pow_two]
  calc a * b * (a * b) = a * ((b * a) * b) := by simp only [mul_assoc]
    _ = a * ((a * b) * b) := by rw [h]
    _ = (a * a) * (b * b) := by simp only [mul_assoc]
    _ = 1 := by rw [ha, hb, one_mul]

theorem pow_three_eq_one_of_braid (ha : a * a = 1) (hb : b * b = 1) (h : a * b * a = b * a * b) :
    (a * b) ^ 3 = 1 := by
  calc (a * b) ^ 3 = (a * b * a) * (b * a * b) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = (b * a * b) * (b * a * b) := by rw [h]
    _ = b * (a * (b * b) * a) * b := by simp only [mul_assoc]
    _ = 1 := by rw [hb, mul_one, ha, mul_one, hb]

theorem commute_of_pow_two (ha : a * a = 1) (hb : b * b = 1) (h : (a * b) ^ 2 = 1) :
    a * b = b * a := by
  rw [pow_two] at h
  rw [eq_inv_of_mul_eq_one_left h, mul_inv_rev, inv_eq_of_mul_eq_one_right ha,
    inv_eq_of_mul_eq_one_right hb]

theorem braid_of_pow_three (ha : a * a = 1) (hb : b * b = 1) (h : (a * b) ^ 3 = 1) :
    a * b * a = b * a * b := by
  have h' : (a * b * a) * (b * a * b) = 1 := by
    rw [← h]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [eq_inv_of_mul_eq_one_left h', mul_inv_rev, mul_inv_rev, inv_eq_of_mul_eq_one_right ha,
    inv_eq_of_mul_eq_one_right hb, mul_assoc]

end GroupLemmas

/-! ### The Coxeter matrix of type `A_n` -/

theorem A_apply {n : ℕ} (i j : Fin n) :
    CoxeterMatrix.A n i j =
      if i = j then 1 else if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then 3 else 2 :=
  rfl

/-! ### The adjacent transpositions satisfy the Coxeter relations -/

variable {n : ℕ}

/-- The adjacent transposition `s_i = (i, i + 1)` of `Fin (n + 1)`. -/
def adjSwap (i : Fin n) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.swap i.castSucc i.succ

theorem adjSwap_mul_self (i : Fin n) : adjSwap i * adjSwap i = 1 :=
  Equiv.swap_mul_self _ _

theorem adjSwap_commute {i j : Fin n} (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    adjSwap i * adjSwap j = adjSwap j * adjSwap i := by
  apply Equiv.Perm.Disjoint.commute
  apply Equiv.Perm.disjoint_swap_swap
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
    and_true, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, not_or, not_false_eq_true]
  omega

theorem adjSwap_braid {i j : Fin n} (h : (i : ℕ) + 1 = j) :
    adjSwap i * adjSwap j * adjSwap i = adjSwap j * adjSwap i * adjSwap j := by
  have hy : j.castSucc = i.succ := Fin.ext (by simp only [Fin.val_castSucc, Fin.val_succ]; omega)
  have h1 : adjSwap j * adjSwap i * adjSwap j = Equiv.swap j.succ i.castSucc := by
    rw [adjSwap, adjSwap, hy]
    exact Equiv.swap_mul_swap_mul_swap Fin.castSucc_lt_succ.ne
      (Fin.ne_of_lt (by rw [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]; omega))
  have h2 : adjSwap i * adjSwap j * adjSwap i = Equiv.swap i.castSucc j.succ := by
    rw [adjSwap, adjSwap, hy, Equiv.swap_comm i.castSucc i.succ, Equiv.swap_comm i.succ j.succ]
    exact Equiv.swap_mul_swap_mul_swap
      (Fin.ne_of_gt (by rw [Fin.lt_def, Fin.val_succ, Fin.val_succ]; omega))
      (Fin.ne_of_gt (by rw [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]; omega))
  rw [h1, h2, Equiv.swap_comm]

theorem isLiftable_adjSwap : (CoxeterMatrix.A n).IsLiftable (adjSwap (n := n)) := by
  intro i j
  rw [A_apply]
  split_ifs with h1 h2
  · subst h1
    rw [pow_one, adjSwap_mul_self]
  · rcases h2 with h2 | h2
    · exact pow_three_eq_one_of_braid (adjSwap_mul_self i) (adjSwap_mul_self j)
        (adjSwap_braid h2).symm
    · exact pow_three_eq_one_of_braid (adjSwap_mul_self i) (adjSwap_mul_self j) (adjSwap_braid h2)
  · have : (i : ℕ) ≠ j := fun h => h1 (Fin.ext h)
    exact pow_two_eq_one_of_commute (adjSwap_mul_self i) (adjSwap_mul_self j)
      (adjSwap_commute (by omega))

variable (n) in
/-- **The homomorphism `W(A_n) → S_{n+1}`**, `s_i ↦ (i, i + 1)`. -/
def toPerm : (CoxeterMatrix.A n).Group →* Equiv.Perm (Fin (n + 1)) :=
  (CoxeterMatrix.A n).toCoxeterSystem.lift ⟨adjSwap, isLiftable_adjSwap⟩

theorem toPerm_simple (i : Fin n) : toPerm n ((CoxeterMatrix.A n).simple i) = adjSwap i :=
  (CoxeterMatrix.A n).toCoxeterSystem.lift_apply_simple isLiftable_adjSwap i

theorem toPerm_surjective : Function.Surjective (toPerm n) := by
  have : MonoidHom.mrange (toPerm n) = ⊤ := by
    apply top_unique
    rw [← Equiv.Perm.mclosure_swap_castSucc_succ n, Submonoid.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨_, toPerm_simple i⟩
  exact MonoidHom.mrange_eq_top.mp this

/-! ### The order of `W(A_n)` -/

variable (n) in
/-- `W(A_n) → W(A_{n+1})`, `s_i ↦ s_i`. -/
def inclusionHom : (CoxeterMatrix.A n).Group →* (CoxeterMatrix.A (n + 1)).Group :=
  (CoxeterMatrix.A n).toCoxeterSystem.lift
    ⟨fun i => (CoxeterMatrix.A (n + 1)).simple i.castSucc, fun i j => by
      have : CoxeterMatrix.A (n + 1) i.castSucc j.castSucc = CoxeterMatrix.A n i j := by
        simp only [A_apply, Fin.castSucc_inj, Fin.val_castSucc]
      rw [← this]
      exact (CoxeterMatrix.A (n + 1)).toCoxeterSystem.simple_mul_simple_pow _ _⟩

theorem inclusionHom_simple (i : Fin n) :
    inclusionHom n ((CoxeterMatrix.A n).simple i) = (CoxeterMatrix.A (n + 1)).simple i.castSucc :=
  (CoxeterMatrix.A n).toCoxeterSystem.lift_apply_simple _ i

variable (n) in
/-- The generators of `W(A_{n+1})`, indexed by `ℕ` (`1` out of range). -/
def simpleGen (j : ℕ) : (CoxeterMatrix.A (n + 1)).Group :=
  if h : j < n + 1 then (CoxeterMatrix.A (n + 1)).simple ⟨j, h⟩ else 1

theorem simpleGen_val (i : Fin (n + 1)) : simpleGen n i = (CoxeterMatrix.A (n + 1)).simple i := by
  rw [simpleGen, dite_eq_left i.isLt]

theorem simpleGen_mul_self (j : ℕ) : simpleGen n j * simpleGen n j = 1 := by
  rw [simpleGen]
  split_ifs
  · exact (CoxeterMatrix.A (n + 1)).toCoxeterSystem.simple_mul_simple_self _
  · rw [one_mul]

theorem simpleGen_commute {i j : ℕ} (hj : j ≤ n) (h : i + 2 ≤ j) :
    simpleGen n i * simpleGen n j = simpleGen n j * simpleGen n i := by
  have hi : i < n + 1 := by omega
  rw [simpleGen, simpleGen, dite_eq_left hi, dite_eq_left (by omega : j < n + 1)]
  apply commute_of_pow_two ((CoxeterMatrix.A (n + 1)).toCoxeterSystem.simple_mul_simple_self _)
    ((CoxeterMatrix.A (n + 1)).toCoxeterSystem.simple_mul_simple_self _)
  have hM : CoxeterMatrix.A (n + 1) ⟨i, hi⟩ ⟨j, by omega⟩ = 2 := by
    rw [A_apply, ite_eq_right (fun e => by rw [Fin.mk.injEq] at e; omega),
      ite_eq_right (by show ¬ (j + 1 = i ∨ i + 1 = j); omega)]
  rw [← hM]
  exact (CoxeterMatrix.A (n + 1)).toCoxeterSystem.simple_mul_simple_pow _ _

theorem simpleGen_braid {i : ℕ} (h : i + 1 ≤ n) :
    simpleGen n i * simpleGen n (i + 1) * simpleGen n i = simpleGen n (i + 1) * simpleGen n i *
        simpleGen n (i + 1) := by
  have hi : i < n + 1 := by omega
  rw [simpleGen, simpleGen, dite_eq_left hi, dite_eq_left (by omega : i + 1 < n + 1)]
  apply braid_of_pow_three ((CoxeterMatrix.A (n + 1)).toCoxeterSystem.simple_mul_simple_self _)
    ((CoxeterMatrix.A (n + 1)).toCoxeterSystem.simple_mul_simple_self _)
  have hM : CoxeterMatrix.A (n + 1) ⟨i, hi⟩ ⟨i + 1, by omega⟩ = 3 := by
    rw [A_apply, ite_eq_right (fun e => by rw [Fin.mk.injEq] at e; omega),
      ite_eq_left (Or.inr rfl)]
  rw [← hM]
  exact (CoxeterMatrix.A (n + 1)).toCoxeterSystem.simple_mul_simple_pow _ _

theorem simpleGen_mem_range {j : ℕ} (hj : j < n) : simpleGen n j ∈ (inclusionHom n).range := by
  refine ⟨(CoxeterMatrix.A n).simple ⟨j, hj⟩, ?_⟩
  rw [inclusionHom_simple, simpleGen, dite_eq_left (by omega)]
  rfl

variable (n) in
/-- The coset representatives `c_k = s_n s_{n-1} ⋯ s_k` (`c_{n+1} = 1`). -/
def cosetRep (k : ℕ) : (CoxeterMatrix.A (n + 1)).Group :=
  if k ≤ n then cosetRep (k + 1) * simpleGen n k else 1
termination_by n + 1 - k

theorem cosetRep_of_le {k : ℕ} (hk : k ≤ n) : cosetRep n k = cosetRep n (k + 1) *
    simpleGen n k := by
  rw [cosetRep, ite_eq_left hk]

theorem cosetRep_of_lt {k : ℕ} (hk : n < k) : cosetRep n k = 1 := by
  rw [cosetRep, ite_eq_right (by omega)]

theorem cosetRep_mul_simpleGen_self {k : ℕ} (hk : k ≤ n) :
    cosetRep n k * simpleGen n k = cosetRep n (k + 1) := by
  rw [cosetRep_of_le hk, mul_assoc, simpleGen_mul_self, mul_one]

theorem cosetRep_mul_simpleGen_pred {k : ℕ} (hk : k ≤ n) :
    cosetRep n (k + 1) * simpleGen n k = cosetRep n k :=
  (cosetRep_of_le hk).symm

/-- `s_j` commutes with `c_k` when `j + 2 ≤ k`. -/
theorem cosetRep_mul_simpleGen_of_le (j : ℕ) :
    ∀ d k, n + 1 - k = d → j + 2 ≤ k → cosetRep n k * simpleGen n j = simpleGen n j *
        cosetRep n k := by
  intro d
  induction d with
  | zero =>
    intro k hd _
    rw [cosetRep_of_lt (k := k) (by omega), one_mul, mul_one]
  | succ d ih =>
    intro k hd hjk
    rw [cosetRep_of_le (k := k) (by omega)]
    calc cosetRep n (k + 1) * simpleGen n k * simpleGen n j = cosetRep n (k + 1) *
           (simpleGen n j * simpleGen n k) := by
          rw [mul_assoc, ← simpleGen_commute (by omega) hjk]
      _ = (cosetRep n (k + 1) * simpleGen n j) * simpleGen n k := by rw [mul_assoc]
      _ = (simpleGen n j * cosetRep n (k + 1)) * simpleGen n k := by
          rw [ih (k + 1) (by omega) (by omega)]
      _ = simpleGen n j * (cosetRep n (k + 1) * simpleGen n k) := by rw [mul_assoc]

/-- `c_k s_j = s_{j-1} c_k` when `k < j ≤ n`. -/
theorem cosetRep_mul_simpleGen_of_lt (j : ℕ) (hj : j ≤ n) :
    ∀ d k, j - 1 - k = d → k < j → cosetRep n k * simpleGen n j = simpleGen n (j - 1) *
        cosetRep n k := by
  intro d
  induction d with
  | zero =>
    intro k hd hkj
    have hk : k + 1 = j := by omega
    subst hk
    rw [Nat.add_sub_cancel, cosetRep_of_le (k := k) (by omega), cosetRep_of_le (k := k + 1) hj]
    have hc := cosetRep_mul_simpleGen_of_le (n := n) k _ (k + 1 + 1) rfl (by omega)
    have hb := simpleGen_braid (n := n) hj
    calc cosetRep n (k + 1 + 1) * simpleGen n (k + 1) * simpleGen n k * simpleGen n (k + 1)
        = cosetRep n (k + 1 + 1) * (simpleGen n (k + 1) * simpleGen n k * simpleGen n (k + 1)) := by
          simp only [mul_assoc]
      _ = cosetRep n (k + 1 + 1) * (simpleGen n k * simpleGen n (k + 1) * simpleGen n k) := by
          rw [hb]
      _ = (cosetRep n (k + 1 + 1) * simpleGen n k) * (simpleGen n (k + 1) * simpleGen n k) := by
          simp only [mul_assoc]
      _ = (simpleGen n k * cosetRep n (k + 1 + 1)) * (simpleGen n (k + 1) * simpleGen n k) := by
          rw [hc]
      _ = simpleGen n k * (cosetRep n (k + 1 + 1) * simpleGen n (k + 1) * simpleGen n k) := by
          simp only [mul_assoc]
  | succ d ih =>
    intro k hd hkj
    rw [cosetRep_of_le (k := k) (by omega)]
    calc cosetRep n (k + 1) * simpleGen n k * simpleGen n j = cosetRep n (k + 1) *
           (simpleGen n j * simpleGen n k) := by
          rw [mul_assoc, simpleGen_commute (i := k) hj (by omega)]
      _ = (cosetRep n (k + 1) * simpleGen n j) * simpleGen n k := by rw [mul_assoc]
      _ = (simpleGen n (j - 1) * cosetRep n (k + 1)) * simpleGen n k := by
          rw [ih (k + 1) (by omega) (by omega)]
      _ = simpleGen n (j - 1) * (cosetRep n (k + 1) * simpleGen n k) := by rw [mul_assoc]

/-- Every element of `W(A_{n+1})` is `h c_k` with `h ∈ W(A_n)`. -/
theorem exists_mul_cosetRep (g : (CoxeterMatrix.A (n + 1)).Group) :
    ∃ h ∈ (inclusionHom n).range, ∃ k ≤ n + 1, g = h * cosetRep n k := by
  refine (CoxeterMatrix.A (n + 1)).toCoxeterSystem.simple_induction_right
    (p := fun g => ∃ h ∈ (inclusionHom n).range, ∃ k ≤ n + 1, g = h * cosetRep n k) g ?_ ?_
  · exact ⟨1, one_mem _, n + 1, le_rfl, by rw [cosetRep_of_lt (k := n + 1) (by omega), one_mul]⟩
  · rintro _ i ⟨h, hh, k, hk, rfl⟩
    rw [CoxeterMatrix.toCoxeterSystem_simple, ← simpleGen_val i, mul_assoc]
    have hj : (i : ℕ) ≤ n := by have := i.isLt; omega
    generalize (i : ℕ) = j at hj ⊢
    rcases lt_trichotomy j k with hjk | hjk | hjk
    · rcases Nat.lt_or_ge (j + 1) k with hjk' | hjk'
      · refine ⟨h * simpleGen n j, mul_mem hh (simpleGen_mem_range (by omega)), k, hk, ?_⟩
        rw [cosetRep_mul_simpleGen_of_le j _ k rfl (by omega), mul_assoc]
      · have hk' : k = j + 1 := by omega
        subst hk'
        exact ⟨h, hh, j, by omega, by rw [cosetRep_mul_simpleGen_pred hj]⟩
    · subst hjk
      exact ⟨h, hh, j + 1, by omega, by rw [cosetRep_mul_simpleGen_self hj]⟩
    · refine ⟨h * simpleGen n (j - 1), mul_mem hh (simpleGen_mem_range (by omega)), k, hk, ?_⟩
      rw [cosetRep_mul_simpleGen_of_lt j hj _ k rfl hjk, mul_assoc]

/-- **`|W(A_n)| ≤ (n + 1)!`**. -/
theorem finite_and_card_le (n : ℕ) :
    Finite (CoxeterMatrix.A n).Group ∧ Nat.card (CoxeterMatrix.A n).Group ≤ (n + 1).factorial := by
  induction n with
  | zero =>
    have : Subsingleton (CoxeterMatrix.A 0).Group := by
      refine ⟨fun a b => ?_⟩
      have h : ∀ g : (CoxeterMatrix.A 0).Group, g = 1 := fun g =>
        (CoxeterMatrix.A 0).toCoxeterSystem.simple_induction_right (p := fun g => g = 1) g rfl
          fun _ i _ => i.elim0
      rw [h a, h b]
    refine ⟨inferInstance, ?_⟩
    rw [zero_add, Nat.factorial_one]
    exact Finite.card_le_one_iff_subsingleton.mpr this
  | succ n ih =>
    obtain ⟨hfin, hcard⟩ := ih
    have hH : Finite (inclusionHom n).range :=
        Finite.of_surjective _ (inclusionHom n).rangeRestrict_surjective
    let F : (inclusionHom n).range × Fin (n + 2) → (CoxeterMatrix.A (n + 1)).Group :=
      fun p => (p.1 : (CoxeterMatrix.A (n + 1)).Group) * cosetRep n p.2
    have hF : Function.Surjective F := by
      intro g
      obtain ⟨h, hh, k, hk, rfl⟩ := exists_mul_cosetRep g
      exact ⟨(⟨h, hh⟩, ⟨k, by omega⟩), rfl⟩
    refine ⟨Finite.of_surjective F hF, ?_⟩
    calc Nat.card (CoxeterMatrix.A (n + 1)).Group ≤ Nat.card
           ((inclusionHom n).range × Fin (n + 2)) :=
          Nat.card_le_card_of_surjective F hF
      _ = Nat.card (inclusionHom n).range * (n + 2) := by rw [Nat.card_prod, Nat.card_fin]
      _ ≤ (n + 1).factorial * (n + 2) := Nat.mul_le_mul_right _
          ((Nat.card_le_card_of_surjective _ (inclusionHom n).rangeRestrict_surjective).trans hcard)
      _ = (n + 1 + 1).factorial := by rw [Nat.factorial_succ (n + 1), mul_comm]

theorem toPerm_bijective : Function.Bijective (toPerm n) := by
  obtain ⟨_, hcard⟩ := finite_and_card_le n
  exact toPerm_surjective.bijective_of_nat_card_le (by rwa [Nat.card_perm, Nat.card_fin])

/-! ### The Coxeter system -/

variable (n) in
/-- **The Coxeter system of type `A_n` on `S_{n+1}`**. -/
noncomputable def permCoxeterSystem :
    CoxeterSystem (CoxeterMatrix.A n) (Equiv.Perm (Fin (n + 1))) :=
  ⟨(MulEquiv.ofBijective (toPerm n) toPerm_bijective).symm⟩

/-- The simple reflections are the adjacent transpositions. -/
theorem permCoxeterSystem_simple (i : Fin n) : (permCoxeterSystem n).simple i = adjSwap i :=
  toPerm_simple i

instance : IsCoxeterGroup (Equiv.Perm (Fin (n + 1))) :=
  ⟨⟨Fin n, CoxeterMatrix.A n, ⟨permCoxeterSystem n⟩⟩⟩

/-! ### Words: adjacent positions and simple reflections -/

/-- The adjacent position of a simple reflection. -/
def toAdj (i : Fin n) : AdjacentPosition (n + 1) :=
  ⟨i.castSucc, by have := i.isLt; simp only [Fin.val_castSucc]; omega⟩

/-- The simple reflection of an adjacent position. -/
def ofAdj (a : AdjacentPosition (n + 1)) : Fin n :=
  ⟨a.left.1, by have := a.hasRight; omega⟩

@[simp]
theorem ofAdj_toAdj (i : Fin n) : ofAdj (toAdj i) = i :=
  Fin.ext rfl

theorem adjacentTransposition_eq (a : AdjacentPosition (n + 1)) :
    adjacentTransposition a = adjSwap (ofAdj a) := by
  rw [adjacentTransposition, adjSwap]
  congr 1

theorem applyRightAdjacentWord_eq (word : List (AdjacentPosition (n + 1)))
    (w : Equiv.Perm (Fin (n + 1))) :
    applyRightAdjacentWord word w = w * (permCoxeterSystem n).wordProd (word.map ofAdj) := by
  induction word generalizing w with
  | nil => simp
  | cons a word ih =>
    rw [applyRightAdjacentWord_cons, ih, List.map_cons, CoxeterSystem.wordProd_cons,
      permCoxeterSystem_simple, ← adjacentTransposition_eq, ← mul_assoc]
    rfl

theorem applyRightAdjacentWord_map_toAdj (ω : List (Fin n)) :
    applyRightAdjacentWord (ω.map toAdj) 1 = (permCoxeterSystem n).wordProd ω := by
  rw [applyRightAdjacentWord_eq, one_mul, List.map_map]
  congr 1
  simp [Function.comp_def]

/-! ### The Coxeter length is the number of inversions -/

theorem length_mul_adjSwap_le (w : Equiv.Perm (Fin (n + 1))) (i : Fin n) :
    FinPermutation.length (w * adjSwap i) ≤ FinPermutation.length w + 1 := by
  have he : w * adjSwap i = FinPermutation.rightAdjacentSwap w (toAdj i) := by
    rw [FinPermutation.rightAdjacentSwap, adjacentTransposition_eq, ofAdj_toAdj]
    rfl
  rw [he]
  rcases descent_or_ascent w (toAdj i) with hd | ha
  · have := length_rightAdjacentSwap_of_descent w (toAdj i) hd
    omega
  · have := length_rightAdjacentSwap_of_ascent w (toAdj i) ha
    omega

theorem length_wordProd_le (ω : List (Fin n)) :
    FinPermutation.length ((permCoxeterSystem n).wordProd ω) ≤ ω.length := by
  induction ω using List.reverseRecOn with
  | nil =>
    have h1 : FinPermutation.length (1 : Equiv.Perm (Fin (n + 1))) = 0 := by
      rw [FinPermutation.length, Finset.card_eq_zero, FinPermutation.inversionSet,
        Finset.filter_eq_empty_iff]
      rintro ⟨a, b⟩ - ⟨h1, h2⟩
      exact lt_asymm h1 h2
    rw [CoxeterSystem.wordProd_nil, h1]
    exact Nat.zero_le _
  | append_singleton ω i ih =>
    rw [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_singleton, permCoxeterSystem_simple,
      List.length_append, List.length_singleton]
    exact (length_mul_adjSwap_le _ i).trans (by omega)

/-- **The Coxeter length on `S_{n+1}` is the number of inversions.** -/
theorem length_eq (w : Equiv.Perm (Fin (n + 1))) :
    (permCoxeterSystem n).length w = FinPermutation.length w := by
  apply le_antisymm
  · obtain ⟨word, hprod, hlen⟩ := exists_reduced_word (n := n + 1) w
    have hw : (permCoxeterSystem n).wordProd (word.map ofAdj) = w := by
      rw [← one_mul ((permCoxeterSystem n).wordProd _), ← applyRightAdjacentWord_eq]
      exact hprod
    calc (permCoxeterSystem n).length w = (permCoxeterSystem n).length
          ((permCoxeterSystem n).wordProd (word.map ofAdj)) := by rw [hw]
      _ ≤ (word.map ofAdj).length := (permCoxeterSystem n).length_wordProd_le _
      _ = FinPermutation.length w := by rw [List.length_map, hlen]
  · obtain ⟨ω, hω, rfl⟩ := (permCoxeterSystem n).exists_isReduced w
    rw [hω.eq]
    exact length_wordProd_le ω

/-! ### The Bruhat order -/

/-- **The rank-matrix order is the subword order of the Coxeter system**: for a reduced word `ω`,
`u ≤ᴮ π ω` iff `u` is the product of a reduced subword of `ω`. -/
theorem strongBruhatLE_iff_exists_reduced_sublist (u : Equiv.Perm (Fin (n + 1)))
    {ω : List (Fin n)} (hω : (permCoxeterSystem n).IsReduced ω) :
    u ≤ᴮ (permCoxeterSystem n).wordProd ω ↔
      ∃ σ : List (Fin n), σ.Sublist ω ∧ (permCoxeterSystem n).IsReduced σ ∧
        (permCoxeterSystem n).wordProd σ = u := by
  have hlen : (ω.map toAdj).length = FinPermutation.length ((permCoxeterSystem n).wordProd ω) := by
    rw [List.length_map, ← length_eq, hω.eq]
  rw [strongBruhatLE_iff_of_reduced u _ (ω.map toAdj) (applyRightAdjacentWord_map_toAdj ω) hlen]
  constructor
  · rintro ⟨sub, hsub, hprod, hsublen⟩
    obtain ⟨σ, hσ, rfl⟩ := List.sublist_map_iff.mp hsub
    have hprod' : (permCoxeterSystem n).wordProd σ = u :=
      (applyRightAdjacentWord_map_toAdj σ).symm.trans hprod
    refine ⟨σ, hσ, ?_, hprod'⟩
    rw [CoxeterSystem.IsReduced, hprod', length_eq, ← hsublen, List.length_map]
  · rintro ⟨σ, hσ, hred, rfl⟩
    refine ⟨σ.map toAdj, hσ.map _, applyRightAdjacentWord_map_toAdj σ, ?_⟩
    rw [List.length_map, ← length_eq, hred.eq]

/-- The same for any reduced word of `v`. -/
theorem strongBruhatLE_iff_of_isReduced (u v : Equiv.Perm (Fin (n + 1))) {ω : List (Fin n)}
    (hω : (permCoxeterSystem n).IsReduced ω) (hv : (permCoxeterSystem n).wordProd ω = v) :
    u ≤ᴮ v ↔ ∃ σ : List (Fin n), σ.Sublist ω ∧ (permCoxeterSystem n).IsReduced σ ∧
      (permCoxeterSystem n).wordProd σ = u := by
  subst hv
  exact strongBruhatLE_iff_exists_reduced_sublist u hω

end FlagVarieties.Bruhat
