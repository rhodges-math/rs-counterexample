import Schubert.RS.Quiver.TwoSource

/-!
# Strict star data

The strict inequalities behind the proof of Corollary 1.5 of the paper. For integer vectors
`A, B, C` (the entries of `a, b, c`), `StarData` collects:

* the strict comparisons that produce the star pattern (5.9): on `{0, 1}` the three sequences
  `a, b, c̄` decrease; from `{0, 1}` to a later position `a` and `c̄` increase and `b` decreases;
  among the later positions `a` and `c̄` decrease and `b` increases;
* positive proper prefix heights;
* the strengthened window inequalities (5.13), `u_j − u_i > h_{i+1}` for every strict increase
  `u_i < u_j`;
* `ν₁ > 0`, `ν₂ > ν₁`, `r_j > 0` and `r_j < ν₂` for `ν = c − a − b = (ν₁, ν₂, −r₁, …)`.

Each of them is strict, so it survives small perturbations, and homogeneous, so it survives
scaling. Under these conditions Proposition 5.8 applies, and the atom coefficient is positive
(`StarData.positive`).
-/

namespace Schubert.RS.Quiver.Density

noncomputable section

open Schubert.RS.Quiver

variable {m : ℕ}

/-- The prefix height `h_k = ∑_{i<k} (C_i − A_i − B_i)` of integer vectors. -/
def heightZ (A B C : Fin (m + 2) → ℤ) (k : ℕ) : ℤ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin (m + 2) => i.val < k), (C i - A i - B i)

/-- The strict inequalities used in the proof of Corollary 1.5. -/
structure StarData (A B C : Fin (m + 2) → ℤ) : Prop where
  nonneg : ∀ i, 0 ≤ A i ∧ 0 ≤ B i ∧ 0 ≤ C i
  balance : ∑ i, C i = ∑ i, A i + ∑ i, B i
  first : A 1 < A 0 ∧ B 1 < B 0 ∧ C 0 < C 1
  pair_single : ∀ i j : Fin (m + 2), i.val < 2 → 2 ≤ j.val → A i < A j ∧ B j < B i ∧ C j < C i
  single_single : ∀ i j : Fin (m + 2), 2 ≤ i.val → i < j → A j < A i ∧ B i < B j ∧ C i < C j
  height_pos : ∀ k, 1 ≤ k → k < m + 2 → 0 < heightZ A B C k
  window_a : ∀ i j : Fin (m + 2), i.val < 2 → 2 ≤ j.val → heightZ A B C (i.val + 1) < A j - A i
  window_b : ∀ i j : Fin (m + 2), 2 ≤ i.val → i < j → heightZ A B C (i.val + 1) < B j - B i
  window_c : ∀ i j : Fin (m + 2), i.val < 2 → 2 ≤ j.val → heightZ A B C (i.val + 1) < C i - C j
  res0 : 0 < C 0 - A 0 - B 0
  res1 : C 0 - A 0 - B 0 < C 1 - A 1 - B 1
  resQ : ∀ j : Fin (m + 2), 2 ≤ j.val →
    C j - A j - B j < 0 ∧ 0 < (C 1 - A 1 - B 1) + (C j - A j - B j)

namespace StarData

variable {A B C : Fin (m + 2) → ℤ} (h : StarData A B C)

include h

theorem castA (i : Fin (m + 2)) : ((A i).toNat : ℤ) = A i := Int.toNat_of_nonneg (h.nonneg i).1
theorem castB (i : Fin (m + 2)) : ((B i).toNat : ℤ) = B i := Int.toNat_of_nonneg (h.nonneg i).2.1
theorem castC (i : Fin (m + 2)) : ((C i).toNat : ℤ) = C i := Int.toNat_of_nonneg (h.nonneg i).2.2

theorem residual_eq (i : Fin (m + 2)) :
    Window.residual (fun i => (A i).toNat) (fun i => (B i).toNat) (fun i => (C i).toNat) i =
      C i - A i - B i := by
  simp only [Window.residual, h.castA, h.castB, h.castC]

theorem prefixHeight_eq (k : ℕ) :
    Window.prefixHeight (fun i => (A i).toNat) (fun i => (B i).toNat) (fun i => (C i).toNat) k =
      heightZ A B C k := by
  unfold Window.prefixHeight heightZ
  exact Finset.sum_congr rfl fun i _ => h.residual_eq i

theorem balance_nat :
    ∑ i, (A i).toNat + ∑ i, (B i).toNat = ∑ i, (C i).toNat := by
  have h1 : ((∑ i, (A i).toNat + ∑ i, (B i).toNat : ℕ) : ℤ) = ((∑ i, (C i).toNat : ℕ) : ℤ) := by
    push_cast
    simp only [h.castA, h.castB, h.castC]
    exact h.balance.symm
  exact_mod_cast h1

/-- Under strict star data, the triple satisfies the hypotheses of Proposition 2.13 for any `N`
bounding `c`. -/
theorem hypotheses (N : ℕ) (hN : ∀ i, C i ≤ N) :
    Window.Hypotheses (fun i => (A i).toNat) (fun i => (B i).toNat) (fun i => (C i).toNat) N := by
  have hA := h.castA
  have hB := h.castB
  have hC := h.castC
  refine ⟨h.balance_nat, fun i => ?_, fun k => ?_, ?_, ?_, ?_⟩
  · have := hN i
    have := hC i
    omega
  · rw [h.prefixHeight_eq]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · simp [heightZ, hk]
    rcases Nat.lt_or_ge k (m + 2) with hk' | hk'
    · exact (h.height_pos k hk hk').le
    · have := Window.prefixHeight_of_le (fun i => (A i).toNat) (fun i => (B i).toNat)
        (fun i => (C i).toNat) hk'
      rw [h.prefixHeight_eq, Window.sum_residual_eq_zero h.balance_nat] at this
      rw [this]
  · intro i j hij hlt
    have hlt' : A i < A j := by have := hA i; have := hA j; simp only at hlt; omega
    refine ⟨i.val, le_rfl, hij, ?_⟩
    rw [h.prefixHeight_eq]
    simp only [hA]
    rcases Nat.lt_or_ge j.val 2 with hj | hj
    · have hi0 : i.val = 0 := by have := Fin.lt_def.mp hij; omega
      have hj1 : j.val = 1 := by have := Fin.lt_def.mp hij; omega
      have e0 : i = 0 := Fin.ext hi0
      have e1 : j = 1 := Fin.ext (by simp [hj1])
      subst e0 e1
      exact absurd h.first.1 (not_lt.mpr hlt'.le)
    rcases Nat.lt_or_ge i.val 2 with hi | hi
    · have := h.window_a i j hi hj
      omega
    · exact absurd (h.single_single i j hi hij).1 (not_lt.mpr hlt'.le)
  · intro i j hij hlt
    have hlt' : B i < B j := by have := hB i; have := hB j; simp only at hlt; omega
    refine ⟨i.val, le_rfl, hij, ?_⟩
    rw [h.prefixHeight_eq]
    simp only [hB]
    rcases Nat.lt_or_ge j.val 2 with hj | hj
    · have hi0 : i.val = 0 := by have := Fin.lt_def.mp hij; omega
      have hj1 : j.val = 1 := by have := Fin.lt_def.mp hij; omega
      have e0 : i = 0 := Fin.ext hi0
      have e1 : j = 1 := Fin.ext (by simp [hj1])
      subst e0 e1
      exact absurd h.first.2.1 (not_lt.mpr hlt'.le)
    rcases Nat.lt_or_ge i.val 2 with hi | hi
    · exact absurd (h.pair_single i j hi hj).2.1 (not_lt.mpr hlt'.le)
    · have := h.window_b i j hi hij
      omega
  · intro i j hij hlt
    have hCi := hC i
    have hCj := hC j
    have hNi := hN i
    have hNj := hN j
    simp only [Window.complement] at hlt
    have hlt' : C j < C i := by omega
    refine ⟨i.val, le_rfl, hij, ?_⟩
    rw [h.prefixHeight_eq]
    simp only [Window.complement]
    rcases Nat.lt_or_ge j.val 2 with hj | hj
    · have hi0 : i.val = 0 := by have := Fin.lt_def.mp hij; omega
      have hj1 : j.val = 1 := by have := Fin.lt_def.mp hij; omega
      have e0 : i = 0 := Fin.ext hi0
      have e1 : j = 1 := Fin.ext (by simp [hj1])
      subst e0 e1
      exact absurd h.first.2.2 (not_lt.mpr hlt'.le)
    rcases Nat.lt_or_ge i.val 2 with hi | hi
    · have := h.window_c i j hi hj
      omega
    · exact absurd (h.single_single i j hi hij).2.2 (not_lt.mpr hlt'.le)

/-- Under strict star data, the comparison weights follow the star pattern (5.9). -/
theorem star (N : ℕ) (hN : ∀ i, C i ≤ N) (i j : Fin (m + 2)) (hij : i < j) :
    Window.cmp
        (Window.triple (fun i => (A i).toNat) (fun i => (B i).toNat)
          (Window.complement N fun i => (C i).toNat) i)
        (Window.triple (fun i => (A i).toNat) (fun i => (B i).toNat)
          (Window.complement N fun i => (C i).toNat) j) = starPattern i j := by
  have hA := h.castA
  have hB := h.castB
  have hC := h.castC
  have hNi := hN i
  have hNj := hN j
  have hAi := hA i
  have hAj := hA j
  have hBi := hB i
  have hBj := hB j
  have hCi := hC i
  have hCj := hC j
  have hij' := Fin.lt_def.mp hij
  simp only [Window.cmp, Window.triple, Window.complement, starPattern]
  rcases Nat.lt_or_ge j.val 2 with hj | hj
  · have hi0 : i.val = 0 := by omega
    have hj1 : j.val = 1 := by omega
    have e0 : i = 0 := Fin.ext hi0
    have e1 : j = 1 := Fin.ext (by simp [hj1])
    subst e0 e1
    obtain ⟨h1, h2, h3⟩ := h.first
    rw [ite_eq_left hj1]
    split_ifs <;> omega
  rcases Nat.lt_or_ge i.val 2 with hi | hi
  · obtain ⟨h1, h2, h3⟩ := h.pair_single i j hi hj
    rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    split_ifs <;> omega
  · obtain ⟨h1, h2, h3⟩ := h.single_single i j hi hij
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    split_ifs <;> omega

/-- **Strict star data give a positive atom coefficient** of a quiver triple (Proposition 5.8). -/
theorem positive (N : ℕ) (hN : ∀ i, C i ≤ N) :
    IsQuiverTriple (fun i => (A i).toNat) (fun i => (B i).toNat) (fun i => (C i).toNat) ∧
      0 < atomCoefficient (key (fun i => (A i).toNat) * key (fun i => (B i).toNat))
        (fun i => (C i).toNat) := by
  have hW := h.hypotheses N hN
  have hS := h.star N hN
  have hN' : ∀ i, (fun i => (C i).toNat) i ≤ N := fun i => by
    have := hN i
    have := h.castC i
    simp only
    omega
  refine ⟨(isQuiverTriple_iff_of_le hN').mpr
    ⟨_, twoSource_isQuiverPartition hW hS⟩, ?_⟩
  have h0 := h.res0
  have h1 := h.res1
  rw [twoSource_pos_iff (ν₁ := (C 0 - A 0 - B 0).toNat) (ν₂ := (C 1 - A 1 - B 1).toNat)
    (r := fun j => (-(C (singletonPos j) - A (singletonPos j) - B (singletonPos j))).toNat)
    (by omega) hW hS]
  · intro j
    have := (h.resQ (singletonPos j) (by simp [singletonPos])).2
    omega
  · rw [h.residual_eq]
    omega
  · rw [h.residual_eq]
    omega
  · intro j
    rw [h.residual_eq]
    have := (h.resQ (singletonPos j) (by simp [singletonPos])).1
    omega

end StarData

end

end Schubert.RS.Quiver.Density
