import RSCounterexample.Paper.Quiver.Density.Seed
import Mathlib.Analysis.Asymptotics.Theta

/-!
# Positive density of quiver triples with positive atom coefficient

Corollary 1.5 of the paper (`cor:intro-quiver-density`). For `n ≥ 4`, let `𝒬⁺_n(H)` be the set of
quiver triples `a, b, c ∈ {0, …, H}^n` with `[𝒜_c](κ_a κ_b) > 0`. Then
`#𝒬⁺_n(H) = Θ(H^{3n−1})`, and these triples form a proportion bounded away from zero among the
triples with `|a| + |b| = |c|`.

The lower bound uses an explicit box instead of the paper's `ε`-argument: with
`t = ⌊H / N₀⌋` and `E₀ = ⌊t / (12 n² + 1)⌋`, every perturbation `t · s + e` of the scaled seed `s`
of (5.12) with `0 ≤ e < E₀` in the `3n − 1` free coordinates (the last entry of `c` is fixed by the
degree equality) has strict star data, hence a positive atom coefficient
(`StarData.positive`), and lies in the box `{0, …, H}^{3n}`. The upper bound counts the triples
satisfying the degree equality: the last entry of `c` is determined by the others.

## Main definitions

* `Schubert.RS.Quiver.Density.positiveQuiverTriples n H`: `𝒬⁺_n(H)`.
* `Schubert.RS.Quiver.Density.balancedTriples n H`: the triples with `|a| + |b| = |c|`.

## Main results

* `Schubert.RS.Quiver.Density.card_positiveQuiverTriples_isTheta`: `#𝒬⁺_n(H) = Θ(H^{3n−1})`.
* `Schubert.RS.Quiver.Density.positiveQuiverTriples_proportion`: the proportion among balanced
  triples is bounded away from zero.
-/

namespace Schubert.RS.Quiver.Density

noncomputable section

open Filter Asymptotics

/-- The triples of weak compositions of length `n` with entries in `{0, …, H}`. -/
def box (n H : ℕ) : Finset (Composition n × Composition n × Composition n) :=
  Fintype.piFinset (fun _ => Finset.range (H + 1)) ×ˢ
    (Fintype.piFinset (fun _ => Finset.range (H + 1)) ×ˢ
      Fintype.piFinset (fun _ => Finset.range (H + 1)))

open scoped Classical in
/-- The triples in the box with `|a| + |b| = |c|`. -/
def balancedTriples (n H : ℕ) : Finset (Composition n × Composition n × Composition n) :=
  (box n H).filter fun x => ∑ i, x.1 i + ∑ i, x.2.1 i = ∑ i, x.2.2 i

open scoped Classical in
/-- `𝒬⁺_n(H)`: the quiver triples in the box with a positive atom coefficient. -/
def positiveQuiverTriples (n H : ℕ) : Finset (Composition n × Composition n × Composition n) :=
  (box n H).filter fun x =>
    IsQuiverTriple x.1 x.2.1 x.2.2 ∧ 0 < atomCoefficient (key x.1 * key x.2.1) x.2.2

theorem positiveQuiverTriples_subset (n H : ℕ) :
    positiveQuiverTriples n H ⊆ balancedTriples n H := by
  classical
  intro x hx
  rw [positiveQuiverTriples, Finset.mem_filter] at hx
  obtain ⟨I, hI⟩ := hx.2.1
  exact Finset.mem_filter.mpr ⟨hx.1, hI.hyp.balance⟩

/-! ## The upper bound -/

theorem card_balancedTriples_le (m H : ℕ) :
    (balancedTriples (m + 2) H).card ≤ (H + 1) ^ (3 * (m + 2) - 1) := by
  classical
  set T := Fintype.piFinset (fun _ : Fin (m + 2) => Finset.range (H + 1)) ×ˢ
    (Fintype.piFinset (fun _ : Fin (m + 2) => Finset.range (H + 1)) ×ˢ
      Fintype.piFinset (fun _ : Fin (m + 1) => Finset.range (H + 1))) with hT
  have hcard : T.card = (H + 1) ^ (3 * (m + 2) - 1) := by
    simp only [hT, Finset.card_product, Fintype.card_piFinset, Finset.card_range,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun x => (x.1, x.2.1, fun i => x.2.2 i.castSucc))
    (fun x hx => ?_) (fun x hx y hy hxy => ?_)
  · simp only [Finset.mem_coe, balancedTriples, Finset.mem_filter, box,
      Finset.mem_product] at hx
    simp only [Finset.mem_coe, hT, Finset.mem_product, Fintype.mem_piFinset] at hx ⊢
    exact ⟨hx.1.1, hx.1.2.1, fun i => hx.1.2.2 _⟩
  · simp only [Finset.mem_coe, balancedTriples, Finset.mem_filter] at hx hy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨ha, hb, hc⟩ := hxy
    have hlast : x.2.2 (Fin.last (m + 1)) = y.2.2 (Fin.last (m + 1)) := by
      have e1 : ∑ i, x.2.2 i = ∑ i, y.2.2 i := by rw [← hx.2, ← hy.2, ha, hb]
      have hcx := Fin.sum_univ_castSucc x.2.2
      have hcy := Fin.sum_univ_castSucc y.2.2
      have hc' : ∑ i : Fin (m + 1), x.2.2 i.castSucc = ∑ i : Fin (m + 1), y.2.2 i.castSucc := by
        rw [hc]
      rw [hcx, hcy, hc'] at e1
      exact Nat.add_left_cancel e1
    refine Prod.ext ha (Prod.ext hb (funext fun i => ?_))
    induction i using Fin.lastCases with
    | last => exact hlast
    | cast j => exact congrFun hc j

/-! ## The family of positive triples -/

variable (m H : ℕ)

/-- The scale `t = ⌊H / N₀⌋`. -/
def scale : ℕ := H / (N₀ m).toNat

/-- The perturbation bound `E₀ = ⌊t / (12 (m + 2)² + 1)⌋`. -/
def pert : ℕ := scale m H / (12 * (m + 2) ^ 2 + 1)

/-- The perturbation of `c`: free in the first `m + 1` positions, the last fixed by the degree
equality. -/
def pertC (fa fb : Fin (m + 2) → Fin (pert m H)) (fc : Fin (m + 1) → Fin (pert m H)) :
    Fin (m + 2) → ℤ :=
  Fin.lastCases (∑ i, ((fa i : ℕ) : ℤ) + ∑ i, ((fb i : ℕ) : ℤ) - ∑ j, ((fc j : ℕ) : ℤ))
    fun j => ((fc j : ℕ) : ℤ)

/-- The perturbed scaled seed, as a triple of weak compositions. -/
def familyTriple (fa fb : Fin (m + 2) → Fin (pert m H)) (fc : Fin (m + 1) → Fin (pert m H)) :
    Composition (m + 2) × Composition (m + 2) × Composition (m + 2) :=
  (fun i => ((scale m H : ℤ) * seedA m i + (fa i : ℕ)).toNat,
    fun i => ((scale m H : ℤ) * seedB m i + (fb i : ℕ)).toNat,
    fun i => ((scale m H : ℤ) * seedC m i + pertC m H fa fb fc i).toNat)

variable {m H}

theorem scale_mul_le (hm : 2 ≤ m) : (scale m H : ℤ) * N₀ m ≤ H := by
  have h1 := one_le_N₀ hm
  have h2 : ((N₀ m).toNat : ℤ) = N₀ m := Int.toNat_of_nonneg (by omega)
  rw [← h2]
  exact_mod_cast Nat.div_mul_le_self H (N₀ m).toNat

theorem abs_pertC_le (fa fb : Fin (m + 2) → Fin (pert m H)) (fc : Fin (m + 1) → Fin (pert m H))
    (i : Fin (m + 2)) : |pertC m H fa fb fc i| ≤ 3 * (m + 2) * (pert m H : ℤ) := by
  have hm0 : (0 : ℤ) ≤ m := by positivity
  have hE0 : (0 : ℤ) ≤ pert m H := by positivity
  induction i using Fin.lastCases with
  | last =>
    simp only [pertC, Fin.lastCases_last]
    have h1 : ∑ i, ((fa i : ℕ) : ℤ) ≤ (m + 2) * pert m H := by
      calc ∑ i, ((fa i : ℕ) : ℤ) ≤ ∑ _i : Fin (m + 2), (pert m H : ℤ) :=
            Finset.sum_le_sum fun i _ => by exact_mod_cast (fa i).isLt.le
        _ = (m + 2) * pert m H := by simp
    have h2 : ∑ i, ((fb i : ℕ) : ℤ) ≤ (m + 2) * pert m H := by
      calc ∑ i, ((fb i : ℕ) : ℤ) ≤ ∑ _i : Fin (m + 2), (pert m H : ℤ) :=
            Finset.sum_le_sum fun i _ => by exact_mod_cast (fb i).isLt.le
        _ = (m + 2) * pert m H := by simp
    have h3 : ∑ j, ((fc j : ℕ) : ℤ) ≤ (m + 1) * pert m H := by
      calc ∑ j, ((fc j : ℕ) : ℤ) ≤ ∑ _j : Fin (m + 1), (pert m H : ℤ) :=
            Finset.sum_le_sum fun j _ => by exact_mod_cast (fc j).isLt.le
        _ = (m + 1) * pert m H := by simp
    have h4 : 0 ≤ ∑ i, ((fa i : ℕ) : ℤ) := Finset.sum_nonneg fun _ _ => by positivity
    have h5 : 0 ≤ ∑ i, ((fb i : ℕ) : ℤ) := Finset.sum_nonneg fun _ _ => by positivity
    have h6 : 0 ≤ ∑ j, ((fc j : ℕ) : ℤ) := Finset.sum_nonneg fun _ _ => by positivity
    rw [abs_le]
    constructor <;> nlinarith
  | cast j =>
    simp only [pertC, Fin.lastCases_castSucc]
    rw [abs_of_nonneg (by positivity)]
    have : ((fc j : ℕ) : ℤ) ≤ pert m H := by exact_mod_cast (fc j).isLt.le
    nlinarith

theorem abs_fin_le (f : Fin (m + 2) → Fin (pert m H)) (i : Fin (m + 2)) :
    |((f i : ℕ) : ℤ)| ≤ 3 * (m + 2) * (pert m H : ℤ) := by
  have hm0 : (0 : ℤ) ≤ m := by positivity
  have hE0 : (0 : ℤ) ≤ pert m H := by positivity
  rw [abs_of_nonneg (by positivity)]
  have : ((f i : ℕ) : ℤ) ≤ pert m H := by exact_mod_cast (f i).isLt.le
  nlinarith

theorem scale_gt (hE : 0 < pert m H) :
    4 * (m + 2) * (3 * (m + 2) * (pert m H : ℤ)) < scale m H := by
  have hmul : (12 * (m + 2) ^ 2 + 1) * pert m H ≤ scale m H := by
    rw [pert, mul_comm]
    exact Nat.div_mul_le_self _ _
  have h' : ((12 * (m + 2) ^ 2 + 1 : ℕ) : ℤ) * (pert m H : ℤ) ≤ (scale m H : ℤ) := by
    exact_mod_cast hmul
  push_cast at h'
  have hE' : (1 : ℤ) ≤ pert m H := by exact_mod_cast hE
  nlinarith

theorem familyTriple_starData (hm : 2 ≤ m) (fa fb : Fin (m + 2) → Fin (pert m H))
    (fc : Fin (m + 1) → Fin (pert m H)) (hE : 0 < pert m H) :
    StarData (fun i => (scale m H : ℤ) * seedA m i + (fa i : ℕ))
      (fun i => (scale m H : ℤ) * seedB m i + (fb i : ℕ))
      (fun i => (scale m H : ℤ) * seedC m i + pertC m H fa fb fc i) := by
  refine starData_perturb hm (scale m H) (3 * (m + 2) * pert m H) _ _ _ (abs_fin_le fa)
    (abs_fin_le fb) (abs_pertC_le fa fb fc) (scale_gt hE) ?_
  rw [Fin.sum_univ_castSucc]
  simp only [pertC, Fin.lastCases_last, Fin.lastCases_castSucc]
  ring

theorem familyTriple_mem (hm : 2 ≤ m) (fa fb : Fin (m + 2) → Fin (pert m H))
    (fc : Fin (m + 1) → Fin (pert m H)) :
    familyTriple m H fa fb fc ∈ positiveQuiverTriples (m + 2) H := by
  classical
  have hE : 0 < pert m H := lt_of_le_of_lt (Nat.zero_le _) (fa 0).isLt
  have hS := familyTriple_starData hm fa fb fc hE
  have hKt := scale_gt (m := m) (H := H) hE
  have hN := scale_mul_le (H := H) hm
  have hm0 : (0 : ℤ) ≤ m := by positivity
  have hE' : (0 : ℤ) ≤ pert m H := by positivity
  have hle : ∀ (s e : ℤ), s ≤ N₀ m - 1 → |e| ≤ 3 * (m + 2) * (pert m H : ℤ) →
      (scale m H : ℤ) * s + e ≤ H := by
    intro s e hs he
    have ht0 : (0 : ℤ) ≤ scale m H := by positivity
    have h1 := (abs_le.mp he).2
    have h2 : 3 * (m + 2) * (pert m H : ℤ) < scale m H := by nlinarith
    have h3 := mul_le_mul_of_nonneg_left hs ht0
    linarith
  have hCle : ∀ i, (scale m H : ℤ) * seedC m i + pertC m H fa fb fc i ≤ H := fun i =>
    hle _ _ (seed_le hm i).2.2 (abs_pertC_le fa fb fc i)
  have hpos := hS.positive H hCle
  refine Finset.mem_filter.mpr ⟨?_, hpos⟩
  simp only [box, familyTriple, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_range,
    Nat.lt_succ_iff]
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
  · have := hle _ _ (seed_le hm i).1 (abs_fin_le fa i)
    omega
  · have := hle _ _ (seed_le hm i).2.1 (abs_fin_le fb i)
    omega
  · have := hCle i
    omega

theorem familyTriple_injective (hm : 2 ≤ m) :
    Function.Injective (fun x : (Fin (m + 2) → Fin (pert m H)) × (Fin (m + 2) → Fin (pert m H)) ×
      (Fin (m + 1) → Fin (pert m H)) => familyTriple m H x.1 x.2.1 x.2.2) := by
  rintro ⟨fa, fb, fc⟩ ⟨fa', fb', fc'⟩ h
  simp only [familyTriple, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hpos : ∀ i, 0 ≤ (scale m H : ℤ) * seedA m i ∧ 0 ≤ (scale m H : ℤ) * seedB m i ∧
      0 ≤ (scale m H : ℤ) * seedC m i := fun i => by
    obtain ⟨a1, a2, a3⟩ := seed_nonneg hm i
    refine ⟨by positivity, by positivity, by positivity⟩
  refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun i => ?_) (funext fun j => ?_))
  · have := congrFun h1 i
    have hp := (hpos i).1
    apply Fin.ext
    dsimp only
    omega
  · have := congrFun h2 i
    have hp := (hpos i).2.1
    apply Fin.ext
    dsimp only
    omega
  · have := congrFun h3 j.castSucc
    have hp := (hpos j.castSucc).2.2
    simp only [pertC, Fin.lastCases_castSucc] at this
    apply Fin.ext
    dsimp only
    omega

theorem pert_pow_le_card (hm : 2 ≤ m) :
    pert m H ^ (3 * (m + 2) - 1) ≤ (positiveQuiverTriples (m + 2) H).card := by
  classical
  have hcard : Fintype.card ((Fin (m + 2) → Fin (pert m H)) × (Fin (m + 2) → Fin (pert m H)) ×
      (Fin (m + 1) → Fin (pert m H))) = pert m H ^ (3 * (m + 2) - 1) := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [← hcard, ← Finset.card_univ]
  exact Finset.card_le_card_of_injOn _ (fun x _ => familyTriple_mem hm x.1 x.2.1 x.2.2)
    (familyTriple_injective hm).injOn

/-! ## Asymptotics -/

theorem pert_eq (m H : ℕ) : pert m H = H / ((N₀ m).toNat * (12 * (m + 2) ^ 2 + 1)) := by
  rw [pert, scale, Nat.div_div_eq_div_mul]

theorem half_le_div {H D : ℕ} (hD : 0 < D) (hH : 2 * D ≤ H) :
    (H : ℝ) / (2 * D) ≤ ((H / D : ℕ) : ℝ) := by
  have h1 := Nat.div_add_mod H D
  have h2 := Nat.mod_lt H hD
  have h3 : (H : ℝ) ≤ 2 * D * (H / D : ℕ) := by
    have : H ≤ 2 * (D * (H / D)) := by omega
    have : (H : ℝ) ≤ 2 * ((D : ℝ) * (H / D : ℕ)) := by exact_mod_cast this
    linarith
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- **Corollary 1.5 of the paper** (`cor:intro-quiver-density`): for `n ≥ 4`, the number of quiver
triples `a, b, c ∈ {0, …, H}^n` with a positive atom coefficient is `Θ(H^{3n−1})`. -/
theorem card_positiveQuiverTriples_isTheta (n : ℕ) (hn : 4 ≤ n) :
    (fun H : ℕ => ((positiveQuiverTriples n H).card : ℝ)) =Θ[atTop]
      fun H : ℕ => (H : ℝ) ^ (3 * n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm : 2 ≤ m := by omega
  set k := 3 * (m + 2) - 1
  set D := (N₀ m).toNat * (12 * (m + 2) ^ 2 + 1) with hD
  have hDpos : 0 < D := by
    have := one_le_N₀ hm
    have : 0 < (N₀ m).toNat := by omega
    positivity
  constructor
  · refine IsBigO.of_bound ((2 : ℝ) ^ k) (eventually_atTop.mpr ⟨1, fun H hH => ?_⟩)
    have hbal := card_balancedTriples_le m H
    have hsub := Finset.card_le_card (positiveQuiverTriples_subset (m + 2) H)
    have h1 : ((positiveQuiverTriples (m + 2) H).card : ℝ) ≤ ((H : ℝ) + 1) ^ k := by
      exact_mod_cast hsub.trans hbal
    have h2 : ((H : ℝ) + 1) ^ k ≤ (2 * (H : ℝ)) ^ k := by
      apply pow_le_pow_left₀ (by positivity)
      have : (1 : ℝ) ≤ H := by exact_mod_cast hH
      linarith
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), ← mul_pow]
    exact h1.trans h2
  · refine IsBigO.of_bound (((2 : ℝ) * D) ^ k) (eventually_atTop.mpr ⟨2 * D, fun H hH => ?_⟩)
    have hlow := pert_pow_le_card (H := H) hm
    rw [pert_eq, ← hD] at hlow
    have h1 : ((H / D : ℕ) : ℝ) ^ k ≤ ((positiveQuiverTriples (m + 2) H).card : ℝ) := by
      exact_mod_cast hlow
    have h2 : ((H : ℝ) / (2 * D)) ^ k ≤ ((H / D : ℕ) : ℝ) ^ k :=
      pow_le_pow_left₀ (by positivity) (half_le_div hDpos hH) k
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    have h3 : (H : ℝ) ^ k = ((2 : ℝ) * D) ^ k * ((H : ℝ) / (2 * D)) ^ k := by
      rw [← mul_pow, mul_div_cancel₀]
      positivity
    rw [h3]
    exact mul_le_mul_of_nonneg_left (h2.trans h1) (by positivity)

/-- **Corollary 1.5**, proportion form: among the triples `a, b, c ∈ {0, …, H}^n` with
`|a| + |b| = |c|`, the quiver triples with a positive atom coefficient form a proportion bounded
away from zero. -/
theorem positiveQuiverTriples_proportion (n : ℕ) (hn : 4 ≤ n) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ H in atTop,
      γ * ((balancedTriples n H).card : ℝ) ≤ ((positiveQuiverTriples n H).card : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm : 2 ≤ m := by omega
  set k := 3 * (m + 2) - 1
  set D := (N₀ m).toNat * (12 * (m + 2) ^ 2 + 1) with hD
  have hDpos : 0 < D := by
    have := one_le_N₀ hm
    have : 0 < (N₀ m).toNat := by omega
    positivity
  refine ⟨1 / ((4 * (D : ℝ)) ^ k), by positivity, eventually_atTop.mpr ⟨2 * D, fun H hH => ?_⟩⟩
  have hH1 : (1 : ℝ) ≤ H := by
    have : 1 ≤ H := by omega
    exact_mod_cast this
  have hbal : ((balancedTriples (m + 2) H).card : ℝ) ≤ (2 * (H : ℝ)) ^ k := by
    have h1 : ((balancedTriples (m + 2) H).card : ℝ) ≤ ((H : ℝ) + 1) ^ k := by
      exact_mod_cast card_balancedTriples_le m H
    exact h1.trans (pow_le_pow_left₀ (by positivity) (by linarith) k)
  have hlow := pert_pow_le_card (H := H) hm
  rw [pert_eq, ← hD] at hlow
  have h1 : ((H / D : ℕ) : ℝ) ^ k ≤ ((positiveQuiverTriples (m + 2) H).card : ℝ) := by
    exact_mod_cast hlow
  have h2 : ((H : ℝ) / (2 * D)) ^ k ≤ ((H / D : ℕ) : ℝ) ^ k :=
    pow_le_pow_left₀ (by positivity) (half_le_div hDpos hH) k
  have h3 : (2 * (H : ℝ)) ^ k = (4 * (D : ℝ)) ^ k * ((H : ℝ) / (2 * D)) ^ k := by
    rw [← mul_pow]
    congr 1
    field_simp
    ring
  calc 1 / (4 * (D : ℝ)) ^ k * ((balancedTriples (m + 2) H).card : ℝ)
      ≤ 1 / (4 * (D : ℝ)) ^ k * (2 * (H : ℝ)) ^ k :=
        mul_le_mul_of_nonneg_left hbal (by positivity)
    _ = ((H : ℝ) / (2 * D)) ^ k := by
        rw [h3]
        field_simp
    _ ≤ _ := h2.trans h1

end

end Schubert.RS.Quiver.Density
