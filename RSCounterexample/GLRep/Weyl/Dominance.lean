import RSCounterexample.GLRep.Weyl.Laurent
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The dominance order on integral weights

For `μ, Λ : Fin n → ℤ`, `μ` is **dominated** by `Λ` (`GLRep.Dominated μ Λ`) when every partial
sum `μ_0 + ⋯ + μ_{k-1}` is at most the corresponding partial sum of `Λ` and the total sums agree;
equivalently, `Λ − μ` is a sum of positive roots `ε_a − ε_b`, `a < b`.

## Main results

* `GLRep.dominated_add`, `GLRep.Dominated.trans`, `GLRep.dominated_add_root`: the order is
  compatible with addition and raising by positive roots.
* `GLRep.dominated_comp_perm`: every rearrangement of a weakly decreasing weight is dominated by
  it.
* `GLRep.eq_of_dominated_of_normSq_eq`: **strict convexity**. If `Λ` is strictly decreasing, `ν`
  is weakly decreasing, `ν` is dominated by `Λ` and `|ν|² = |Λ|²`, then `ν = Λ`.
-/

namespace GLRep

open Finset

variable {n : ℕ}

/-- The partial sum `μ_0 + ⋯ + μ_{k-1}`. -/
def partialSum (μ : Fin n → ℤ) (k : ℕ) : ℤ := ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < k), μ i

/-- `μ` is **dominated** by `Λ`: `Λ − μ` is a sum of positive roots. -/
def Dominated (μ Λ : Fin n → ℤ) : Prop :=
  (∀ k, partialSum μ k ≤ partialSum Λ k) ∧ ∑ i, μ i = ∑ i, Λ i

theorem partialSum_add (μ ν : Fin n → ℤ) (k : ℕ) :
    partialSum (μ + ν) k = partialSum μ k + partialSum ν k := by
  simp [partialSum, sum_add_distrib]

theorem partialSum_of_le {μ : Fin n → ℤ} {k : ℕ} (hk : n ≤ k) : partialSum μ k = ∑ i, μ i := by
  rw [partialSum, filter_true_of_mem fun i _ => lt_of_lt_of_le i.isLt hk]

theorem dominated_refl (μ : Fin n → ℤ) : Dominated μ μ := ⟨fun _ => le_rfl, rfl⟩

theorem Dominated.trans {μ ν Λ : Fin n → ℤ} (h₁ : Dominated μ ν) (h₂ : Dominated ν Λ) :
    Dominated μ Λ :=
  ⟨fun k => (h₁.1 k).trans (h₂.1 k), h₁.2.trans h₂.2⟩

theorem dominated_add {μ Λ μ' Λ' : Fin n → ℤ} (h : Dominated μ Λ) (h' : Dominated μ' Λ') :
    Dominated (μ + μ') (Λ + Λ') :=
  ⟨fun k => by rw [partialSum_add, partialSum_add]; exact add_le_add (h.1 k) (h'.1 k), by
    simp only [Pi.add_apply, sum_add_distrib, h.2, h'.2]⟩

/-- Raising by a positive root `ε_a − ε_b`, `a < b`, raises in the dominance order. -/
theorem dominated_add_root (μ : Fin n → ℤ) {a b : Fin n} (hab : a < b) :
    Dominated μ (μ + (Pi.single a 1 - Pi.single b 1)) := by
  refine ⟨fun k => ?_, ?_⟩
  · rw [partialSum_add, le_add_iff_nonneg_right]
    simp only [partialSum, Pi.sub_apply, sum_sub_distrib, sub_nonneg]
    rw [sum_pi_single', sum_pi_single']
    simp only [mem_filter, mem_univ, true_and]
    split_ifs with hb ha <;> simp_all
    omega
  · simp [sum_add_distrib, sum_sub_distrib]

/-- The partial sum over the first `k ≤ n` indices, as a sum over `Fin k`. -/
theorem partialSum_eq_sum_castLE (μ : Fin n → ℤ) {k : ℕ} (hk : k ≤ n) :
    partialSum μ k = ∑ j : Fin k, μ (Fin.castLE hk j) := by
  classical
  refine Eq.trans ?_ (Finset.sum_map univ (Fin.castLEEmb hk) μ)
  rw [partialSum]
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, mem_map, Fin.castLEEmb_apply]
  constructor
  · intro hi
    exact ⟨⟨i, hi⟩, rfl⟩
  · rintro ⟨j, rfl⟩
    exact j.isLt

/-- The sum of a weakly decreasing `λ` over a set of `k` indices is at most its sum over the first
`k` indices. -/
theorem sum_le_partialSum {lam : Fin n → ℤ} (hlam : Antitone lam) (S : Finset (Fin n)) :
    ∑ i ∈ S, lam i ≤ partialSum lam S.card := by
  classical
  set k := S.card
  have hk : k ≤ n := by simpa using S.card_le_univ
  set e := S.orderEmbOfFin (k := k) rfl
  have hS : ∑ i ∈ S, lam i = ∑ j : Fin k, lam (e j) := by
    refine Eq.trans ?_ (Finset.sum_map univ e.toEmbedding lam)
    congr 1
    ext i
    simp only [mem_map, mem_univ, true_and, RelEmbedding.coe_toEmbedding]
    constructor
    · intro hi
      have : i ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact hi
      exact this
    · rintro ⟨j, rfl⟩
      exact Finset.orderEmbOfFin_mem S rfl j
  have hge : ∀ m (hm : m < k), m ≤ (e ⟨m, hm⟩ : ℕ) := by
    intro m
    induction m with
    | zero => exact fun _ => Nat.zero_le _
    | succ m ih =>
      intro hm
      have h1 := ih (Nat.lt_of_succ_lt hm)
      have h2 : e ⟨m, Nat.lt_of_succ_lt hm⟩ < e ⟨m + 1, hm⟩ :=
        e.strictMono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self m))
      exact Nat.succ_le_of_lt (lt_of_le_of_lt h1 h2)
  rw [hS, partialSum_eq_sum_castLE lam hk]
  exact Finset.sum_le_sum fun j _ => hlam (Fin.le_def.mpr (hge j j.isLt))

/-- **Every rearrangement of a weakly decreasing weight is dominated by it.** -/
theorem dominated_comp_perm {lam : Fin n → ℤ} (hlam : Antitone lam) (σ : Equiv.Perm (Fin n)) :
    Dominated (lam ∘ σ) lam := by
  classical
  refine ⟨fun k => ?_, Equiv.sum_comp σ lam⟩
  set T := univ.filter (fun i : Fin n => (i : ℕ) < k)
  have h1 : partialSum (lam ∘ σ) k = ∑ i ∈ T.map σ.toEmbedding, lam i := by
    rw [Finset.sum_map]
    rfl
  rw [h1]
  refine (sum_le_partialSum hlam _).trans (le_of_eq ?_)
  rw [Finset.card_map]
  by_cases hk : k ≤ n
  · rw [partialSum_eq_sum_castLE lam hk]
    have : T.card = k := by
      rw [show T = (univ : Finset (Fin k)).map (Fin.castLEEmb hk) from ?_, card_map, card_univ,
        Fintype.card_fin]
      ext i
      simp only [T, mem_filter, mem_univ, true_and, mem_map, Fin.castLEEmb_apply]
      exact ⟨fun hi => ⟨⟨i, hi⟩, rfl⟩, by rintro ⟨j, rfl⟩; exact j.isLt⟩
    rw [this, partialSum_eq_sum_castLE lam hk]
  · push Not at hk
    have hT : T = univ := filter_true_of_mem fun i _ => lt_trans i.isLt hk
    rw [hT, card_univ, Fintype.card_fin, partialSum_of_le le_rfl, partialSum_of_le hk.le]

/-- Summation by parts. -/
theorem sum_range_sub_mul (D s : ℕ → ℤ) (m : ℕ) :
    ∑ i ∈ range m, (D (i + 1) - D i) * s i =
      D m * s m - D 0 * s 0 + ∑ i ∈ range m, D (i + 1) * (s i - s (i + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih, sum_range_succ]
    ring

theorem partialSum_succ (μ : Fin n → ℤ) (i : Fin n) :
    partialSum μ (i + 1) = partialSum μ i + μ i := by
  classical
  rw [add_comm (partialSum μ i), partialSum, partialSum, ← sum_insert (by simp)]
  congr 1
  ext j
  simp only [mem_filter, mem_univ, true_and, mem_insert]
  constructor
  · intro hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
    · exact Or.inr h
    · exact Or.inl (Fin.ext h)
  · rintro (rfl | h)
    · exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt h

theorem partialSum_zero (μ : Fin n → ℤ) : partialSum μ 0 = 0 := by
  simp [partialSum]

/-- **Strict convexity of the norm on the dominance order.** -/
theorem eq_of_dominated_of_normSq_eq {ν Λ : Fin n → ℤ} (hΛ : StrictAnti Λ) (hν : Antitone ν)
    (hd : Dominated ν Λ) (hnorm : LaurentPoly.normSq ν = LaurentPoly.normSq Λ) : ν = Λ := by
  classical
  -- extend to sequences indexed by `ℕ`
  let ext : (Fin n → ℤ) → ℕ → ℤ := fun μ i => if h : i < n then μ ⟨i, h⟩ else 0
  let D : ℕ → ℤ := fun k => partialSum Λ k - partialSum ν k
  let s : ℕ → ℤ := fun i => ext Λ i + ext ν i
  have hD : ∀ k, 0 ≤ D k := fun k => sub_nonneg.mpr (hd.1 k)
  have hD0 : D 0 = 0 := by simp [D, partialSum_zero]
  have hDn : D n = 0 := by simp only [D, partialSum_of_le le_rfl, hd.2, sub_self]
  have hstep : ∀ i : Fin n, D (i + 1) - D i = Λ i - ν i := by
    intro i
    simp only [D, partialSum_succ]
    ring
  -- the norm difference, summed by parts
  have hsum : ∑ i ∈ range n, D (i + 1) * (s i - s (i + 1)) = 0 := by
    have h1 : LaurentPoly.normSq Λ - LaurentPoly.normSq ν =
        ∑ i ∈ range n, (D (i + 1) - D i) * s i := by
      rw [LaurentPoly.normSq, LaurentPoly.normSq, ← sum_sub_distrib,
        ← Fin.sum_univ_eq_sum_range (fun i => (D (i + 1) - D i) * s i)]
      refine sum_congr rfl fun i _ => ?_
      rw [hstep i]
      simp only [s, ext, i.isLt, ↓reduceDIte]
      ring
    rw [sum_range_sub_mul, hD0, hDn, zero_mul, zero_mul, sub_zero, zero_add] at h1
    rw [← h1, hnorm, sub_self]
  -- every term is nonnegative, so every term vanishes
  have hgap : ∀ i, i + 1 < n → 0 < s i - s (i + 1) := by
    intro i hi
    have h1 : Λ ⟨i + 1, hi⟩ < Λ ⟨i, by omega⟩ := hΛ (Fin.mk_lt_mk.mpr (Nat.lt_succ_self i))
    have h2 : ν ⟨i + 1, hi⟩ ≤ ν ⟨i, by omega⟩ := hν (Fin.mk_le_mk.mpr (Nat.le_succ i))
    simp only [s, ext, hi, show i < n by omega, ↓reduceDIte]
    linarith
  have hterm : ∀ i ∈ range n, 0 ≤ D (i + 1) * (s i - s (i + 1)) := by
    intro i hi
    rcases Nat.lt_or_ge (i + 1) n with h | h
    · exact mul_nonneg (hD _) (hgap i h).le
    · have : i + 1 = n := by have := mem_range.mp hi; omega
      rw [this, hDn, zero_mul]
  have hzero := (sum_eq_zero_iff_of_nonneg hterm).mp hsum
  have hDz : ∀ k, k ≤ n → D k = 0 := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact hD0
    rcases Nat.lt_or_ge k n with h | h
    · obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
      have := hzero i (mem_range.mpr (by omega))
      exact (mul_eq_zero.mp this).resolve_right (hgap i h).ne'
    · rw [show k = n by omega, hDn]
  funext i
  have := hstep i
  rw [hDz _ (by omega), hDz _ i.isLt.le, sub_zero] at this
  linarith

end GLRep
