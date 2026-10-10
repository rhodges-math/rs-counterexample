import RSCounterexample.Paper.Window.Basic
import RSCounterexample.Paper.RootSeriesWindow
import RSCounterexample.Paper.CombinedRootFactors
import RSCounterexample.Paper.AtomCoefficients
import RSCounterexample.Paper.JosephPolo.GeneralTheorem
import RSCounterexample.Paper.PBW.Theorem

/-!
# Proposition 2.13: the rational extraction formula

For weak compositions `a b c` of length `n` with `|a| + |b| = |c|`, an integer `N ≥ max c`,
nonnegative prefix heights `h_k` and the window inequalities (2.12) for `a`, `b` and
`c̄ = N·1 − c`, Proposition 2.13 (`prop:window`) of the paper states (2.14):

  `[𝒜_c](κ_a κ_b) = [x^{c−a−b}] ∏_{i<j} (1 − x_i/x_j)^{−cmp((a_i,b_i,c̄_i),(a_j,b_j,c̄_j))}`,

with each factor `(1 − x_i/x_j)^{−1}` expanded as a geometric series.

Every monomial of the product lies in the positive-root cone, so the formula is stated in the
simple-root coordinates `y_k = x_k/x_{k+1}`. There `x_i/x_j = y^{rootDegree i j}`, the factor
`(1 − x_i/x_j)^{−k}` is `cmpFactor k (rootDegree i j)`, and `x^{c−a−b} = y^h` with `h` the prefix
heights (`heightDegree`, with `rootWeight (heightDegree a b c) = c − a − b`).

## Main definitions

* `Schubert.RS.Window.heightDegree`: the prefix heights as simple-root coordinates.
* `Schubert.RS.Window.cmpFactor`: `(1 − X^d)^{−k}` as a formal power series.

## Main results

* `Schubert.RS.Window.window_rational_extraction`: Proposition 2.13, (2.14).
* `Schubert.RS.Window.rootWeight_heightDegree`: `heightDegree` encodes `c − a − b`.
* `Schubert.RS.Window.window_product_indep`: the right side of (2.14) does not depend on `N`.

The proof assembles the key-atom duality (`atomCoefficient_eq_rectangleCoefficient`), the
three-key window theorem (`three_key_window_coefficient`) and the cancellation of the three
ascent denominators against the Weyl factor (`three_root_series_eq_product`). The Joseph–Polo
presentation, the Demazure character formula and the ordered PBW basis enter through their proved
forms `compositionFlagJosephPolo`, `compositionFlagDemazureCharacter` and
`orderedPBWBasis_exists`.
-/

namespace Schubert.RS.Window

noncomputable section

open Representation

variable {n : ℕ}

/-! ## Prefix heights as simple-root coordinates -/

section Heights

variable (a b c : Composition n)

theorem prefixHeight_zero : prefixHeight a b c 0 = 0 := by
  simp [prefixHeight]

theorem prefixHeight_of_le {k : ℕ} (hk : n ≤ k) :
    prefixHeight a b c k = ∑ i, residual a b c i := by
  unfold prefixHeight
  rw [Finset.filter_true_of_mem fun i _ => lt_of_lt_of_le i.isLt hk]

theorem prefixHeight_succ (j : Fin n) :
    prefixHeight a b c (j.val + 1) = prefixHeight a b c j.val + residual a b c j := by
  unfold prefixHeight
  have he : Finset.univ.filter (fun i : Fin n => i.val < j.val + 1) =
      insert j (Finset.univ.filter fun i : Fin n => i.val < j.val) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [he, Finset.sum_insert (by simp), add_comm]

variable {a b c}

theorem sum_residual_eq_zero (hbal : ∑ i, a i + ∑ i, b i = ∑ i, c i) :
    ∑ i, residual a b c i = 0 := by
  have h := congrArg (fun m : ℕ => (m : ℤ)) hbal
  simp only [Nat.cast_add, Nat.cast_sum] at h
  simp only [residual, Finset.sum_sub_distrib]
  linarith

/-- The prefix heights `h_1, …, h_{n−1}` as simple-root coordinates. -/
def heightDegree (a b c : Composition n) : RootDegree n :=
  Finsupp.equivFunOnFinite.symm fun k : Fin (n - 1) => (prefixHeight a b c (k.val + 1)).toNat

@[simp] theorem heightDegree_apply (k : Fin (n - 1)) :
    heightDegree a b c k = (prefixHeight a b c (k.val + 1)).toNat := by
  simp [heightDegree]

theorem extendedRootDegree_heightDegree (hbal : ∑ i, a i + ∑ i, b i = ∑ i, c i)
    (hnn : ∀ k, 0 ≤ prefixHeight a b c k) (k : Fin (n + 1)) :
    extendedRootDegree (heightDegree a b c) k = prefixHeight a b c k.val := by
  unfold extendedRootDegree
  split_ifs with h
  · rw [heightDegree_apply]
    have hk : k.val - 1 + 1 = k.val := by omega
    simp only [hk, Int.toNat_of_nonneg (hnn _)]
  · rcases Nat.eq_zero_or_pos k.val with h0 | hpos
    · rw [h0, prefixHeight_zero]
    · have hk : n ≤ k.val := by omega
      rw [prefixHeight_of_le a b c hk, sum_residual_eq_zero hbal]

/-- The simple-root coordinates `heightDegree a b c` encode the residual weight `c − a − b`. -/
theorem rootWeight_heightDegree (hbal : ∑ i, a i + ∑ i, b i = ∑ i, c i)
    (hnn : ∀ k, 0 ≤ prefixHeight a b c k) :
    rootWeight (heightDegree a b c) = residual a b c := by
  rw [rootWeight_discrete]
  funext j
  simp only [extendedRootDegree_heightDegree hbal hnn, Fin.val_succ, Fin.val_castSucc,
    prefixHeight_succ]
  ring

end Heights

/-! ## The factors `(1 − x_i/x_j)^{−cmp}` -/

/-- `(1 − X^d)^{−k}` as a formal power series: the `k`-th power of the geometric series
`∑_{r ≥ 0} X^{r d}` for `k ≥ 0`, and `(1 − X^d)^{−k}` for `k < 0`. -/
def cmpFactor {σ : Type*} (k : ℤ) (d : σ →₀ ℕ) : MvPowerSeries σ ℤ :=
  if 0 ≤ k then rootGeometricSeries d ^ k.toNat else (1 - MvPowerSeries.monomial d 1) ^ (-k).toNat

/-- The combined factor of the three ascent series and the Weyl factor at a positive root is
`(1 − x_i/x_j)^{−cmp}` (the last step of the proof of Proposition 2.13). -/
theorem combinedRootFactor_eq_cmpFactor (a b g : Composition n) (r : PositiveRoot n) :
    combinedRootFactor a b g r =
      cmpFactor (cmp (triple a b g r.val.1) (triple a b g r.val.2))
        (rootDegree r.val.1 r.val.2) := by
  classical
  have hd : rootDegree r.val.1 r.val.2 ≠ 0 := by
    intro h
    have hc := rootDegree_first r.val.1 r.val.2 r.property
    rw [h] at hc
    simp at hc
  unfold combinedRootFactor cmpFactor cmp triple
  generalize rootDegree r.val.1 r.val.2 = d at hd ⊢
  have hi := rootGeometricSeries_mul d hd
  by_cases hA : a r.val.1 < a r.val.2 <;> by_cases hB : b r.val.1 < b r.val.2 <;>
    by_cases hC : g r.val.1 < g r.val.2 <;>
    simp only [hA, hB, hC, ↓reduceIte] <;> norm_num <;>
    first
      | ring1
      | linear_combination hi
      | linear_combination rootGeometricSeries d * hi
      | linear_combination rootGeometricSeries d ^ 2 * hi

/-! ## Proposition 2.13 -/

/-- A window inequality excludes the omitted Joseph–Polo relation at every ascent. -/
theorem not_jpExponent_smul_le {a b c : Composition n} (hnn : ∀ k, 0 ≤ prefixHeight a b c k)
    {u : Composition n} (hu : WindowInequality u (prefixHeight a b c))
    (r : PositiveRoot n) (hr : u r.val.1 < u r.val.2) :
    ¬ jpExponent u r • rootDegree r.val.1 r.val.2 ≤ heightDegree a b c := by
  obtain ⟨k, hik, hkj, hlt⟩ := hu r.val.1 r.val.2 r.property hr
  intro hle
  have hk : k < n - 1 := by
    have := r.val.2.isLt
    omega
  have h1 := hle ⟨k, hk⟩
  simp only [Finsupp.smul_apply, smul_eq_mul, rootDegree_apply, heightDegree_apply, hik, hkj,
    and_self, ↓reduceIte, mul_one] at h1
  have h2 := Int.toNat_of_nonneg (hnn (k + 1))
  unfold jpExponent at h1
  omega

theorem three_keys_target {a b c : Composition n} {N : ℕ} (h : Hypotheses a b c N) :
    (fun i => (a i : ℤ) + b i + (complement N c i : ℤ)) + rootWeight (heightDegree a b c) =
      fun _ => (N : ℤ) := by
  rw [rootWeight_heightDegree h.balance h.height_nonneg]
  funext i
  simp only [Pi.add_apply, residual, complement_cast h.le_N]
  ring

/-- **Proposition 2.13** (`prop:window`), the rational extraction formula (2.14). Under the
hypotheses of the proposition,
`[𝒜_c](κ_a κ_b) = [x^{c−a−b}] ∏_{i<j} (1 − x_i/x_j)^{−cmp((a_i,b_i,c̄_i),(a_j,b_j,c̄_j))}`,
written in the simple-root coordinates of the positive-root cone: `x_i/x_j` is the monomial of
`rootDegree i j`, and `x^{c−a−b}` is the monomial of `heightDegree a b c`
(`rootWeight_heightDegree`). -/
theorem window_rational_extraction {a b c : Composition n} {N : ℕ} (h : Hypotheses a b c N) :
    atomCoefficient (key a * key b) c =
      MvPowerSeries.coeff (heightDegree a b c)
        (∏ r : PositiveRoot n, cmpFactor (cmp (triple a b (complement N c) r.val.1)
          (triple a b (complement N c) r.val.2)) (rootDegree r.val.1 r.val.2)) := by
  rw [atomCoefficient_eq_rectangleCoefficient compositionFlagJosephPolo
    compositionFlagDemazureCharacter (orderedPBWBasis_exists n) N c h.le_N]
  have hw := three_key_window_coefficient compositionFlagTorus compositionFlagGenerator
    compositionFlagJosephPolo compositionFlagDemazureCharacter (orderedPBWBasis_exists n)
    a b (complement N c) (heightDegree a b c)
    (not_jpExponent_smul_le h.height_nonneg h.window_a)
    (not_jpExponent_smul_le h.height_nonneg h.window_b)
    (not_jpExponent_smul_le h.height_nonneg h.window_c)
  rw [three_keys_target h, three_root_series_eq_product] at hw
  unfold rectangleCoefficient
  rw [map_mul]
  refine hw.trans ?_
  exact congrArg _ (Finset.prod_congr rfl fun r _ => combinedRootFactor_eq_cmpFactor _ _ _ r)

/-- The right side of (2.14) does not depend on the choice of `N ≥ max c` (the remark after
(2.12)). -/
theorem window_product_indep (a b : Composition n) {c : Composition n} {N N' : ℕ}
    (hN : ∀ i, c i ≤ N) (hN' : ∀ i, c i ≤ N') :
    (∏ r : PositiveRoot n, cmpFactor (cmp (triple a b (complement N c) r.val.1)
        (triple a b (complement N c) r.val.2)) (rootDegree r.val.1 r.val.2)) =
      ∏ r : PositiveRoot n, cmpFactor (cmp (triple a b (complement N' c) r.val.1)
        (triple a b (complement N' c) r.val.2)) (rootDegree r.val.1 r.val.2) :=
  Finset.prod_congr rfl fun r _ => by rw [cmp_complement_eq a b hN hN']

end

end Schubert.RS.Window
