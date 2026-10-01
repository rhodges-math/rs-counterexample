import Schubert.RS.Quiver.Density.Star

/-!
# The seed of the density argument

The triple (5.12) of the paper, for `n = m + 2 ≥ 4`, in 0-based positions: with `δ = 10(m + 2)`
and `N₀ = (4m + 21)δ + 10m`,

* `(a₀, b₀, c̄₀) = ((2m + 10)δ + 1, (2m + 10)δ + 1, δ + 1)`,
* `(a₁, b₁, c̄₁) = ((2m + 10)δ − 1, (2m + 10)δ − 1, δ − 1)`,
* `(a_i, b_i, c̄_i) = ((3m + 15 − i)δ, (2i + 1)δ, (m + 6 − i)δ)` for `2 ≤ i ≤ m + 1`,

and `c = N₀ − c̄`. Then `ν = c − a − b = (10m − 3, 10m + 3, −20, …, −20)`, the proper prefix heights
are `10m − 3` and `20(m + 2 − k)`, and every inequality of `StarData` holds with margin at least
`1` (`seed_*`). For a scaled and perturbed seed `t · s + e` with `|e_i| ≤ E` and `4(m + 2)E < t`,
every inequality still holds (`starData_perturb`).
-/

namespace Schubert.RS.Quiver.Density

noncomputable section

variable (m : ℕ)

/-- `δ = 10(m + 2)`. -/
def δ : ℤ := 10 * ((m : ℤ) + 2)

/-- `N₀ = (4m + 21)δ + 10m`. -/
def N₀ : ℤ := (4 * m + 21) * δ m + 10 * m

/-- The seed `a` of (5.12). -/
def seedA (i : Fin (m + 2)) : ℤ :=
  if i.val = 0 then (2 * m + 10) * δ m + 1 else if i.val = 1 then (2 * m + 10) * δ m - 1
  else (3 * m + 15 - i.val) * δ m

/-- The seed `b` of (5.12). -/
def seedB (i : Fin (m + 2)) : ℤ :=
  if i.val = 0 then (2 * m + 10) * δ m + 1 else if i.val = 1 then (2 * m + 10) * δ m - 1
  else (2 * i.val + 1) * δ m

/-- The seed `c̄` of (5.12). -/
def seedCbar (i : Fin (m + 2)) : ℤ :=
  if i.val = 0 then δ m + 1 else if i.val = 1 then δ m - 1 else (m + 6 - i.val) * δ m

/-- The seed `c = N₀ − c̄`. -/
def seedC (i : Fin (m + 2)) : ℤ := N₀ m - seedCbar m i

variable {m}

theorem δ_eq : δ m = 10 * (m : ℤ) + 20 := by
  unfold δ
  ring

theorem seed_res (i : Fin (m + 2)) :
    seedC m i - seedA m i - seedB m i =
      if i.val = 0 then 10 * (m : ℤ) - 3 else if i.val = 1 then 10 * (m : ℤ) + 3 else -20 := by
  unfold seedC seedA seedB seedCbar N₀
  rw [δ_eq]
  split_ifs <;> ring

/-! ## Prefix heights -/

theorem heightZ_zero (A B C : Fin (m + 2) → ℤ) : heightZ A B C 0 = 0 := by
  simp [heightZ]

theorem heightZ_succ (A B C : Fin (m + 2) → ℤ) (k : ℕ) (hk : k < m + 2) :
    heightZ A B C (k + 1) = heightZ A B C k + (C ⟨k, hk⟩ - A ⟨k, hk⟩ - B ⟨k, hk⟩) := by
  unfold heightZ
  have he : Finset.univ.filter (fun i : Fin (m + 2) => i.val < k + 1) =
      insert ⟨k, hk⟩ (Finset.univ.filter fun i : Fin (m + 2) => i.val < k) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [he, Finset.sum_insert (by simp), add_comm]

theorem seed_height_one : heightZ (seedA m) (seedB m) (seedC m) 1 = 10 * (m : ℤ) - 3 := by
  rw [heightZ_succ _ _ _ 0 (by omega), heightZ_zero, seed_res]
  simp

theorem seed_height (k : ℕ) (hk : 2 ≤ k) (hkm : k ≤ m + 2) :
    heightZ (seedA m) (seedB m) (seedC m) k = 20 * ((m : ℤ) + 2 - k) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have hk1 : k = 1 := by omega
      subst hk1
      rw [heightZ_succ _ _ _ 1 (by omega), seed_height_one, seed_res]
      simp only [one_ne_zero, ↓reduceIte]
      push_cast
      ring
    · rw [heightZ_succ _ _ _ k (by omega), ih hk2 (by omega), seed_res]
      simp only [show k ≠ 0 by omega, show k ≠ 1 by omega, ↓reduceIte]
      push_cast
      ring

theorem seed_height_bounds (hm : 2 ≤ m) (k : ℕ) (hk : 1 ≤ k) (hkm : k < m + 2) :
    1 ≤ heightZ (seedA m) (seedB m) (seedC m) k ∧
      heightZ (seedA m) (seedB m) (seedC m) k ≤ 20 * m := by
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have : k = 1 := by omega
    subst this
    rw [seed_height_one]
    constructor <;> omega
  · rw [seed_height k hk2 hkm.le]
    constructor <;> omega

theorem seed_balance :
    ∑ i, seedC m i = ∑ i, seedA m i + ∑ i, seedB m i := by
  have h := seed_height (m := m) (m + 2) (by omega) le_rfl
  have hfull : heightZ (seedA m) (seedB m) (seedC m) (m + 2) =
      ∑ i, (seedC m i - seedA m i - seedB m i) := by
    unfold heightZ
    rw [Finset.filter_true_of_mem fun i _ => i.isLt]
  rw [hfull] at h
  simp only [Finset.sum_sub_distrib] at h
  push_cast at h
  linarith

/-! ## The seed inequalities -/

theorem seedA_of_zero {i : Fin (m + 2)} (h : i.val = 0) :
    seedA m i = (2 * m + 10) * (10 * (m : ℤ) + 20) + 1 := by
  simp [seedA, h, δ_eq]

theorem seedA_of_one {i : Fin (m + 2)} (h : i.val = 1) :
    seedA m i = (2 * m + 10) * (10 * (m : ℤ) + 20) - 1 := by
  simp [seedA, h, δ_eq]

theorem seedA_of_two_le {i : Fin (m + 2)} (h : 2 ≤ i.val) :
    seedA m i = (3 * m + 15 - i.val) * (10 * (m : ℤ) + 20) := by
  simp [seedA, show i.val ≠ 0 by omega, show i.val ≠ 1 by omega, δ_eq]

theorem seedB_of_zero {i : Fin (m + 2)} (h : i.val = 0) :
    seedB m i = (2 * m + 10) * (10 * (m : ℤ) + 20) + 1 := by
  simp [seedB, h, δ_eq]

theorem seedB_of_one {i : Fin (m + 2)} (h : i.val = 1) :
    seedB m i = (2 * m + 10) * (10 * (m : ℤ) + 20) - 1 := by
  simp [seedB, h, δ_eq]

theorem seedB_of_two_le {i : Fin (m + 2)} (h : 2 ≤ i.val) :
    seedB m i = (2 * i.val + 1) * (10 * (m : ℤ) + 20) := by
  simp [seedB, show i.val ≠ 0 by omega, show i.val ≠ 1 by omega, δ_eq]

theorem seedC_of_zero {i : Fin (m + 2)} (h : i.val = 0) :
    seedC m i = N₀ m - (10 * (m : ℤ) + 20 + 1) := by
  simp [seedC, seedCbar, h, δ_eq]

theorem seedC_of_one {i : Fin (m + 2)} (h : i.val = 1) :
    seedC m i = N₀ m - (10 * (m : ℤ) + 20 - 1) := by
  simp [seedC, seedCbar, h, δ_eq]

theorem seedC_of_two_le {i : Fin (m + 2)} (h : 2 ≤ i.val) :
    seedC m i = N₀ m - (m + 6 - i.val) * (10 * (m : ℤ) + 20) := by
  simp [seedC, seedCbar, show i.val ≠ 0 by omega, show i.val ≠ 1 by omega, δ_eq]

theorem N₀_eq : N₀ m = (4 * m + 21) * (10 * (m : ℤ) + 20) + 10 * m := by
  simp [N₀, δ_eq]

theorem seed_first :
    1 ≤ seedA m 0 - seedA m 1 ∧ 1 ≤ seedB m 0 - seedB m 1 ∧ 1 ≤ seedC m 1 - seedC m 0 := by
  rw [seedA_of_zero (i := 0) rfl, seedA_of_one (i := 1) (by simp), seedB_of_zero (i := 0) rfl,
    seedB_of_one (i := 1) (by simp), seedC_of_zero (i := 0) rfl, seedC_of_one (i := 1) (by simp)]
  refine ⟨by linarith, by linarith, by linarith⟩

section SeedFacts

variable (hm : 2 ≤ m)
include hm

theorem seed_nonneg (i : Fin (m + 2)) : 1 ≤ seedA m i ∧ 1 ≤ seedB m i ∧ 1 ≤ seedC m i := by
  have hi := i.isLt
  have hm' : (2 : ℤ) ≤ m := by exact_mod_cast hm
  have hiv : (i.val : ℤ) ≤ m + 1 := by exact_mod_cast (Nat.lt_succ_iff.mp hi)
  have hN := N₀_eq (m := m)
  rcases Nat.lt_or_ge i.val 2 with hi2 | hi2
  · rcases Nat.lt_or_ge i.val 1 with hi1 | hi1
    · rw [seedA_of_zero (by omega), seedB_of_zero (by omega), seedC_of_zero (by omega)]
      refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
    · rw [seedA_of_one (by omega), seedB_of_one (by omega), seedC_of_one (by omega)]
      refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
  · have hi2' : (2 : ℤ) ≤ i.val := by exact_mod_cast hi2
    rw [seedA_of_two_le hi2, seedB_of_two_le hi2, seedC_of_two_le hi2]
    refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

theorem seed_pair_single (i j : Fin (m + 2)) (hi : i.val < 2) (hj : 2 ≤ j.val) :
    1 ≤ seedA m j - seedA m i ∧ 1 ≤ seedB m i - seedB m j ∧ 1 ≤ seedC m i - seedC m j := by
  have hjm := j.isLt
  have hm' : (2 : ℤ) ≤ m := by exact_mod_cast hm
  have hjv : (j.val : ℤ) ≤ m + 1 := by exact_mod_cast (Nat.lt_succ_iff.mp hjm)
  have hj2 : (2 : ℤ) ≤ j.val := by exact_mod_cast hj
  rw [seedA_of_two_le hj, seedB_of_two_le hj, seedC_of_two_le hj]
  rcases Nat.lt_or_ge i.val 1 with hi1 | hi1
  · rw [seedA_of_zero (by omega), seedB_of_zero (by omega), seedC_of_zero (by omega)]
    refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
  · rw [seedA_of_one (by omega), seedB_of_one (by omega), seedC_of_one (by omega)]
    refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

theorem seed_single_single (i j : Fin (m + 2)) (hi : 2 ≤ i.val) (hij : i < j) :
    1 ≤ seedA m i - seedA m j ∧ 1 ≤ seedB m j - seedB m i ∧ 1 ≤ seedC m j - seedC m i := by
  have hij' := Fin.lt_def.mp hij
  have hj : 2 ≤ j.val := by omega
  have hlt : (i.val : ℤ) + 1 ≤ j.val := by exact_mod_cast hij'
  have hm' : (0 : ℤ) ≤ m := by positivity
  rw [seedA_of_two_le hi, seedB_of_two_le hi, seedC_of_two_le hi, seedA_of_two_le hj,
    seedB_of_two_le hj, seedC_of_two_le hj]
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

theorem seed_window_a (i j : Fin (m + 2)) (hi : i.val < 2) (hj : 2 ≤ j.val) :
    1 ≤ seedA m j - seedA m i - heightZ (seedA m) (seedB m) (seedC m) (i.val + 1) := by
  have hh := (seed_height_bounds hm (i.val + 1) (by omega) (by omega)).2
  have hjm := j.isLt
  have hm' : (2 : ℤ) ≤ m := by exact_mod_cast hm
  have hjv : (j.val : ℤ) ≤ m + 1 := by exact_mod_cast (Nat.lt_succ_iff.mp hjm)
  rw [seedA_of_two_le hj]
  rcases Nat.lt_or_ge i.val 1 with hi1 | hi1
  · rw [seedA_of_zero (by omega)]
    nlinarith
  · rw [seedA_of_one (by omega)]
    nlinarith

theorem seed_window_b (i j : Fin (m + 2)) (hi : 2 ≤ i.val) (hij : i < j) :
    1 ≤ seedB m j - seedB m i - heightZ (seedA m) (seedB m) (seedC m) (i.val + 1) := by
  have hij' := Fin.lt_def.mp hij
  have hjm := j.isLt
  have hh := (seed_height_bounds hm (i.val + 1) (by omega) (by omega)).2
  have hlt : (i.val : ℤ) + 1 ≤ j.val := by exact_mod_cast hij'
  have hm' : (0 : ℤ) ≤ m := by positivity
  rw [seedB_of_two_le hi, seedB_of_two_le (by omega)]
  nlinarith

theorem seed_window_c (i j : Fin (m + 2)) (hi : i.val < 2) (hj : 2 ≤ j.val) :
    1 ≤ seedC m i - seedC m j - heightZ (seedA m) (seedB m) (seedC m) (i.val + 1) := by
  have hh := (seed_height_bounds hm (i.val + 1) (by omega) (by omega)).2
  have hjm := j.isLt
  have hm' : (2 : ℤ) ≤ m := by exact_mod_cast hm
  have hjv : (j.val : ℤ) ≤ m + 1 := by exact_mod_cast (Nat.lt_succ_iff.mp hjm)
  rw [seedC_of_two_le hj]
  rcases Nat.lt_or_ge i.val 1 with hi1 | hi1
  · rw [seedC_of_zero (by omega)]
    nlinarith
  · rw [seedC_of_one (by omega)]
    nlinarith

theorem seed_res_facts :
    1 ≤ seedC m 0 - seedA m 0 - seedB m 0 ∧
      1 ≤ (seedC m 1 - seedA m 1 - seedB m 1) - (seedC m 0 - seedA m 0 - seedB m 0) ∧
      ∀ j : Fin (m + 2), 2 ≤ j.val → 1 ≤ -(seedC m j - seedA m j - seedB m j) ∧
        1 ≤ (seedC m 1 - seedA m 1 - seedB m 1) + (seedC m j - seedA m j - seedB m j) := by
  have hm' : (2 : ℤ) ≤ m := by exact_mod_cast hm
  have h0 := seed_res (m := m) 0
  have h1 := seed_res (m := m) 1
  simp only [Fin.val_zero, ↓reduceIte] at h0
  simp only [Fin.val_one, one_ne_zero, ↓reduceIte] at h1
  refine ⟨by omega, by omega, fun j hj => ?_⟩
  have hjr := seed_res (m := m) j
  simp only [show j.val ≠ 0 by omega, show j.val ≠ 1 by omega, ↓reduceIte] at hjr
  omega

theorem seed_le (i : Fin (m + 2)) :
    seedA m i ≤ N₀ m - 1 ∧ seedB m i ≤ N₀ m - 1 ∧ seedC m i ≤ N₀ m - 1 := by
  have hi := i.isLt
  have hm' : (2 : ℤ) ≤ m := by exact_mod_cast hm
  have hiv : (i.val : ℤ) ≤ m + 1 := by exact_mod_cast (Nat.lt_succ_iff.mp hi)
  have hN := N₀_eq (m := m)
  rcases Nat.lt_or_ge i.val 2 with hi2 | hi2
  · rcases Nat.lt_or_ge i.val 1 with hi1 | hi1
    · rw [seedA_of_zero (by omega), seedB_of_zero (by omega), seedC_of_zero (by omega)]
      refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
    · rw [seedA_of_one (by omega), seedB_of_one (by omega), seedC_of_one (by omega)]
      refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
  · have hi2' : (2 : ℤ) ≤ i.val := by exact_mod_cast hi2
    rw [seedA_of_two_le hi2, seedB_of_two_le hi2, seedC_of_two_le hi2]
    refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

theorem one_le_N₀ : 1 ≤ N₀ m := by
  have hN := N₀_eq (m := m)
  have hm' : (2 : ℤ) ≤ m := by exact_mod_cast hm
  nlinarith

end SeedFacts

/-! ## Perturbations of the scaled seed -/

theorem margin {s e t K : ℤ} (hs : 1 ≤ s) (he : |e| ≤ K) (hK : K < t) : 0 < t * s + e := by
  have ht : 0 < t := lt_of_le_of_lt ((abs_nonneg e).trans he) hK
  have := abs_le.mp he
  nlinarith

theorem heightZ_perturb (t : ℤ) (sA sB sC ea eb ec : Fin (m + 2) → ℤ) (k : ℕ) :
    heightZ (fun i => t * sA i + ea i) (fun i => t * sB i + eb i) (fun i => t * sC i + ec i) k =
      t * heightZ sA sB sC k + heightZ ea eb ec k := by
  unfold heightZ
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem abs_heightZ_le (ea eb ec : Fin (m + 2) → ℤ) {E : ℤ} (hea : ∀ i, |ea i| ≤ E)
    (heb : ∀ i, |eb i| ≤ E) (hec : ∀ i, |ec i| ≤ E) (k : ℕ) :
    |heightZ ea eb ec k| ≤ 3 * (m + 2) * E := by
  unfold heightZ
  have hE : 0 ≤ E := (abs_nonneg _).trans (hea 0)
  calc |∑ i ∈ Finset.univ.filter (fun i : Fin (m + 2) => i.val < k), (ec i - ea i - eb i)|
      ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin (m + 2) => i.val < k), |ec i - ea i - eb i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin (m + 2) => i.val < k), 3 * E :=
        Finset.sum_le_sum fun i _ => by
          have h1 := abs_le.mp (hea i)
          have h2 := abs_le.mp (heb i)
          have h3 := abs_le.mp (hec i)
          rw [abs_le]
          constructor <;> linarith
    _ ≤ ∑ _i : Fin (m + 2), 3 * E :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ => by positivity
    _ = 3 * (m + 2) * E := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- **Scaled and perturbed seeds have strict star data**: for `|e_i| ≤ E` and `4(m + 2)E < t`. -/
theorem starData_perturb (hm : 2 ≤ m) (t E : ℤ) (ea eb ec : Fin (m + 2) → ℤ)
    (hea : ∀ i, |ea i| ≤ E) (heb : ∀ i, |eb i| ≤ E) (hec : ∀ i, |ec i| ≤ E)
    (ht : 4 * (m + 2) * E < t) (hbal : ∑ i, ec i = ∑ i, ea i + ∑ i, eb i) :
    StarData (fun i => t * seedA m i + ea i) (fun i => t * seedB m i + eb i)
      (fun i => t * seedC m i + ec i) := by
  have hE : 0 ≤ E := (abs_nonneg _).trans (hea 0)
  have hm2 : (0 : ℤ) ≤ m := by positivity
  have hK2 : 2 * E < t := by nlinarith
  have hK3 : 3 * E < t := by nlinarith
  have hK6 : 6 * E < t := by nlinarith
  have hKh : 3 * (m + 2) * E + 2 * E < t := by nlinarith
  have hKr : 3 * (m + 2) * E < t := by nlinarith
  -- differences of perturbations
  have hd : ∀ (e : Fin (m + 2) → ℤ), (∀ i, |e i| ≤ E) → ∀ i j, |e i - e j| ≤ 2 * E := by
    intro e he i j
    have h1 := abs_le.mp (he i)
    have h2 := abs_le.mp (he j)
    rw [abs_le]
    constructor <;> linarith
  have hd3 : ∀ i, |ec i - ea i - eb i| ≤ 3 * E := by
    intro i
    have h1 := abs_le.mp (hea i)
    have h2 := abs_le.mp (heb i)
    have h3 := abs_le.mp (hec i)
    rw [abs_le]
    constructor <;> linarith
  refine ⟨fun i => ?_, ?_, ?_, fun i j hi hj => ?_, fun i j hi hij => ?_, fun k hk hkm => ?_,
    fun i j hi hj => ?_, fun i j hi hij => ?_, fun i j hi hj => ?_, ?_, ?_, fun j hj => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := seed_nonneg hm i
    have e1 := abs_le.mp (hea i)
    have e2 := abs_le.mp (heb i)
    have e3 := abs_le.mp (hec i)
    refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
  · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, seed_balance, hbal]
    ring
  · obtain ⟨h1, h2, h3⟩ := seed_first (m := m)
    refine ⟨?_, ?_, ?_⟩
    · have := margin h1 (hd ea hea 0 1) hK2
      linarith
    · have := margin h2 (hd eb heb 0 1) hK2
      linarith
    · have := margin h3 (hd ec hec 1 0) hK2
      linarith
  · obtain ⟨h1, h2, h3⟩ := seed_pair_single hm i j hi hj
    refine ⟨?_, ?_, ?_⟩
    · have := margin h1 (hd ea hea j i) hK2
      linarith
    · have := margin h2 (hd eb heb i j) hK2
      linarith
    · have := margin h3 (hd ec hec i j) hK2
      linarith
  · obtain ⟨h1, h2, h3⟩ := seed_single_single hm i j hi hij
    refine ⟨?_, ?_, ?_⟩
    · have := margin h1 (hd ea hea i j) hK2
      linarith
    · have := margin h2 (hd eb heb j i) hK2
      linarith
    · have := margin h3 (hd ec hec j i) hK2
      linarith
  · rw [heightZ_perturb]
    exact margin (seed_height_bounds hm k hk hkm).1 (abs_heightZ_le ea eb ec hea heb hec k) hKr
  · rw [heightZ_perturb]
    have hs := seed_window_a hm i j hi hj
    have hb := abs_heightZ_le ea eb ec hea heb hec (i.val + 1)
    have hdd := hd ea hea j i
    have := margin hs (show |(ea j - ea i) - heightZ ea eb ec (i.val + 1)| ≤
      3 * (m + 2) * E + 2 * E by
        calc _ ≤ |ea j - ea i| + |heightZ ea eb ec (i.val + 1)| := abs_sub _ _
          _ ≤ _ := by linarith) hKh
    linarith
  · rw [heightZ_perturb]
    have hs := seed_window_b hm i j hi hij
    have hb := abs_heightZ_le ea eb ec hea heb hec (i.val + 1)
    have hdd := hd eb heb j i
    have := margin hs (show |(eb j - eb i) - heightZ ea eb ec (i.val + 1)| ≤
      3 * (m + 2) * E + 2 * E by
        calc _ ≤ |eb j - eb i| + |heightZ ea eb ec (i.val + 1)| := abs_sub _ _
          _ ≤ _ := by linarith) hKh
    linarith
  · rw [heightZ_perturb]
    have hs := seed_window_c hm i j hi hj
    have hb := abs_heightZ_le ea eb ec hea heb hec (i.val + 1)
    have hdd := hd ec hec i j
    have := margin hs (show |(ec i - ec j) - heightZ ea eb ec (i.val + 1)| ≤
      3 * (m + 2) * E + 2 * E by
        calc _ ≤ |ec i - ec j| + |heightZ ea eb ec (i.val + 1)| := abs_sub _ _
          _ ≤ _ := by linarith) hKh
    linarith
  · have := margin (seed_res_facts hm).1 (hd3 0) hK3
    linarith
  · have h6 : |(ec 1 - ea 1 - eb 1) - (ec 0 - ea 0 - eb 0)| ≤ 6 * E := by
      calc _ ≤ |ec 1 - ea 1 - eb 1| + |ec 0 - ea 0 - eb 0| := abs_sub _ _
        _ ≤ _ := by linarith [hd3 0, hd3 1]
    have := margin (seed_res_facts hm).2.1 h6 hK6
    linarith
  · obtain ⟨h1, h2⟩ := (seed_res_facts hm).2.2 j hj
    have h6 : |(ec 1 - ea 1 - eb 1) + (ec j - ea j - eb j)| ≤ 6 * E := by
      calc _ ≤ |ec 1 - ea 1 - eb 1| + |ec j - ea j - eb j| := abs_add_le _ _
        _ ≤ _ := by linarith [hd3 1, hd3 j]
    have h3' : |-(ec j - ea j - eb j)| ≤ 3 * E := by rw [abs_neg]; exact hd3 j
    refine ⟨?_, ?_⟩
    · have := margin h1 h3' hK3
      linarith
    · have := margin h2 h6 hK6
      linarith

end

end Schubert.RS.Quiver.Density
