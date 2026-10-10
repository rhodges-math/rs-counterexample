import RSCounterexample.Paper.Quiver.Schur.Projector
import RSCounterexample.Paper.Quiver.CompleteWindow

/-!
# The Pieri rule in alternant form

For a weakly decreasing `κ` and `s ≥ 0`,

`a_{κ+δ} · h_s = ∑_w a_{κ+w+δ}`,

the sum over the exponent vectors `w` of `h_s` such that `κ + w` interlaces `κ`, that is
`κ_i + w_i ≤ κ_{i−1}` for `i ≥ 1` (`alternant_mul_hsymm_pieri`). Multiplying `a_{κ+δ}` by
`h_s = ∑_{|w| = s} x^w` gives `∑_{|w| = s} a_{κ+δ+w}`; the terms that break interlacing cancel in
pairs, by exchanging the entries `i − 1` and `i` of `κ + δ + w` at the largest index `i` where
interlacing fails.

## Main definitions

* `Schubert.RS.Quiver.Schur.compositionsOf`: the exponent vectors of `h_s`.
* `Schubert.RS.Quiver.Schur.pieriSet`: those keeping `κ + w` interlaced with `κ`.

## Main results

* `Schubert.RS.Quiver.Schur.toLaurent_hsymm`: `h_s` as a sum of monomials.
* `Schubert.RS.Quiver.Schur.alternant_mul_hsymm_pieri`: the Pieri rule.
* `Schubert.RS.Quiver.Schur.antitone_add_of_mem_pieriSet`: the new exponents are weakly decreasing.
-/

namespace Schubert.RS.Quiver.Schur

noncomputable section

open Equiv

variable {d : ℕ}

/-- A vector of natural numbers as a weight. -/
def liftW (w : Fin d → ℕ) : Weight d := fun i => (w i : ℤ)

@[simp] theorem liftW_apply (w : Fin d → ℕ) (i : Fin d) : liftW w i = (w i : ℤ) := rfl

/-! ## `h_s` as a sum of monomials -/

/-- The exponent vectors of the monomials of `h_s` in `d` variables. -/
def compositionsOf (d s : ℕ) : Finset (Fin d → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range (s + 1)).filter fun w => ∑ i, w i = s

theorem mem_compositionsOf {s : ℕ} {w : Fin d → ℕ} :
    w ∈ compositionsOf d s ↔ ∑ i, w i = s := by
  simp only [compositionsOf, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range,
    and_iff_right_iff_imp]
  intro h i
  have := Finset.single_le_sum (fun j _ => Nat.zero_le (w j)) (Finset.mem_univ i)
  omega

theorem hsymm_eq_sum (s : ℕ) :
    MvPolynomial.hsymm (Fin d) ℤ s = ∑ w ∈ compositionsOf d s,
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm w) 1 := by
  classical
  ext α
  rw [coeff_hsymm, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, Equiv.symm_apply_eq]
  rw [Finset.sum_ite_eq']
  simp [mem_compositionsOf]

/-- **`h_s` as a sum of monomials** in `Laurent d`. -/
theorem toLaurent_hsymm (s : ℕ) :
    toLaurent (MvPolynomial.hsymm (Fin d) ℤ s) =
      ∑ w ∈ compositionsOf d s, AddMonoidAlgebra.single (liftW w) 1 := by
  rw [hsymm_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [toLaurent_monomial]
  rfl

theorem isSymmetric_toLaurent_hsymm (s : ℕ) :
    IsSymmetric (toLaurent (MvPolynomial.hsymm (Fin d) ℤ s)) :=
  isSymmetric_toLaurent (MvPolynomial.hsymm_isSymmetric (Fin d) ℤ s)

theorem alternant_mul_hsymm (α : Weight d) (s : ℕ) :
    alternant α * toLaurent (MvPolynomial.hsymm (Fin d) ℤ s) =
      ∑ w ∈ compositionsOf d s, alternant (α + liftW w) := by
  have hS := isSymmetric_toLaurent_hsymm (d := d) s
  rw [toLaurent_hsymm] at hS ⊢
  exact alternant_mul_sum_single α _ liftW hS

/-! ## Interlacing and the cancelling involution -/

/-- The previous index `i − 1` (with `0 ↦ 0`). -/
def prev (i : Fin d) : Fin d := ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩

theorem prev_val (i : Fin d) : (prev i).val = i.val - 1 := rfl

theorem prev_ne {i : Fin d} (hi : 0 < i.val) : prev i ≠ i := fun h => by
  have := congrArg Fin.val h
  rw [prev_val] at this
  omega

theorem prev_le (i : Fin d) : prev i ≤ i := Fin.le_def.mpr (Nat.sub_le _ _)

theorem staircase_prev {i : Fin d} (hi : 0 < i.val) :
    staircase d (prev i) = staircase d i + 1 := by
  simp only [staircase, prev_val]
  have : ((i.val - 1 : ℕ) : ℤ) = (i.val : ℤ) - 1 := by omega
  rw [this]
  ring

/-- Adding `w` to `κ` breaks interlacing at `i ≥ 1`: `κ_i + w_i > κ_{i−1}`. -/
def Violates (κ : Weight d) (w : Fin d → ℕ) (i : Fin d) : Prop :=
  0 < i.val ∧ κ (prev i) < κ i + w i

instance (κ : Weight d) (w : Fin d → ℕ) : DecidablePred (Violates κ w) := fun _ => by
  unfold Violates
  infer_instance

/-- The exponent vectors `w` of `h_s` for which `κ + w` interlaces `κ`. -/
def pieriSet (κ : Weight d) (s : ℕ) : Finset (Fin d → ℕ) :=
  (compositionsOf d s).filter fun w => ∀ i, ¬ Violates κ w i

/-- For `w` in the Pieri set, `κ + w` is weakly decreasing. -/
theorem antitone_add_of_mem_pieriSet {κ : Weight d} (hκ : Antitone κ) {s : ℕ} {w : Fin d → ℕ}
    (hw : w ∈ pieriSet κ s) : Antitone (κ + liftW w) := by
  intro i k hik
  have hv := (Finset.mem_filter.mp hw).2
  rcases eq_or_lt_of_le hik with h | h
  · rw [h]
  · have hk : 0 < k.val := lt_of_le_of_lt (Nat.zero_le _) h
    have h1 : κ k + w k ≤ κ (prev k) := by
      by_contra hc
      exact hv k ⟨hk, lt_of_not_ge hc⟩
    have h2 : κ (prev k) ≤ κ i :=
      hκ (Fin.le_def.mpr (by rw [prev_val]; have := Fin.lt_def.mp h; omega))
    simp only [Pi.add_apply, liftW_apply]
    have := (w i).cast_nonneg (α := ℤ)
    linarith

/-- Exchanging the entries `i − 1` and `i` of `κ + δ + w`, written as a new exponent vector. -/
def swapW (κ : Weight d) (w : Fin d → ℕ) (i : Fin d) : Fin d → ℕ := fun k =>
  if k = prev i then (κ i + w i - κ (prev i) - 1).toNat
  else if k = i then (κ (prev i) + w (prev i) - κ i + 1).toNat
  else w k

section Involution

variable {κ : Weight d} (hκ : Antitone κ) {w : Fin d → ℕ} {i : Fin d}

theorem swapW_prev_cast (hv : Violates κ w i) :
    ((swapW κ w i (prev i) : ℕ) : ℤ) = κ i + w i - κ (prev i) - 1 := by
  have h : swapW κ w i (prev i) = (κ i + w i - κ (prev i) - 1).toNat := by simp [swapW]
  rw [h, Int.toNat_of_nonneg (by have := hv.2; omega)]

include hκ in
theorem swapW_self_cast (hv : Violates κ w i) :
    ((swapW κ w i i : ℕ) : ℤ) = κ (prev i) + w (prev i) - κ i + 1 := by
  have h : swapW κ w i i = (κ (prev i) + w (prev i) - κ i + 1).toNat := by
    simp [swapW, (prev_ne hv.1).symm]
  have h1 : κ i ≤ κ (prev i) := hκ (prev_le i)
  have h2 := (w (prev i)).cast_nonneg (α := ℤ)
  rw [h, Int.toNat_of_nonneg (by omega)]

theorem swapW_of_ne {k : Fin d} (h1 : k ≠ prev i) (h2 : k ≠ i) : swapW κ w i k = w k := by
  simp [swapW, h1, h2]

include hκ in
/-- **The exchange**: the new exponent vector realizes `κ + δ + w` with the entries `i − 1` and `i`
exchanged. -/
theorem add_swapW (hv : Violates κ w i) :
    κ + liftW (swapW κ w i) + staircase d =
      (κ + liftW w + staircase d) ∘ ⇑(Equiv.swap (prev i) i) := by
  funext k
  simp only [Pi.add_apply, liftW_apply, Function.comp_apply]
  by_cases hk : k = prev i
  · subst hk
    rw [Equiv.swap_apply_left, swapW_prev_cast hv, staircase_prev hv.1]
    ring
  · by_cases hk' : k = i
    · subst hk'
      rw [Equiv.swap_apply_right, swapW_self_cast hκ hv, staircase_prev hv.1]
      ring
    · rw [Equiv.swap_apply_of_ne_of_ne hk hk', swapW_of_ne hk hk']

include hκ in
theorem sum_swapW (hv : Violates κ w i) : ∑ k, swapW κ w i k = ∑ k, w k := by
  have h := congrArg (fun β : Weight d => ∑ k, β k) (add_swapW hκ hv)
  simp only [Function.comp_apply] at h
  rw [Equiv.sum_comp (Equiv.swap (prev i) i) (κ + liftW w + staircase d)] at h
  simp only [Pi.add_apply, liftW_apply, Finset.sum_add_distrib] at h
  have h' : ((∑ k, swapW κ w i k : ℕ) : ℤ) = ((∑ k, w k : ℕ) : ℤ) := by
    push_cast
    linarith
  exact_mod_cast h'

include hκ in
theorem violates_swapW (hv : Violates κ w i) : Violates κ (swapW κ w i) i := by
  refine ⟨hv.1, ?_⟩
  rw [swapW_self_cast hκ hv]
  have := (w (prev i)).cast_nonneg (α := ℤ)
  linarith

theorem violates_swapW_iff_of_lt {k : Fin d} (hik : i < k) :
    Violates κ (swapW κ w i) k ↔ Violates κ w k := by
  have h1 : k ≠ prev i := fun h => absurd (h ▸ prev_le i) (not_le.mpr hik)
  have h2 : k ≠ i := (ne_of_lt hik).symm
  simp only [Violates, swapW_of_ne h1 h2]

include hκ in
theorem swapW_swapW (hv : Violates κ w i) : swapW κ (swapW κ w i) i = w := by
  have hv' := violates_swapW hκ hv
  funext k
  by_cases hk : k = prev i
  · rw [hk]
    have h := swapW_prev_cast hv'
    rw [swapW_self_cast hκ hv] at h
    have h' : ((swapW κ (swapW κ w i) i (prev i) : ℕ) : ℤ) = (w (prev i) : ℤ) := by
      rw [h]
      ring
    exact_mod_cast h'
  · by_cases hk' : k = i
    · rw [hk']
      have h := swapW_self_cast hκ hv'
      rw [swapW_prev_cast hv] at h
      have h' : ((swapW κ (swapW κ w i) i i : ℕ) : ℤ) = (w i : ℤ) := by
        rw [h]
        ring
      exact_mod_cast h'
    · rw [swapW_of_ne hk hk', swapW_of_ne hk hk']

end Involution

/-- An alternant with two equal exponents vanishes. -/
theorem alternant_eq_zero_of_comp_swap {β : Weight d} {i j : Fin d} (hij : i ≠ j)
    (h : β ∘ ⇑(Equiv.swap i j) = β) : alternant β = 0 := by
  have h1 := alternant_comp_perm β (Equiv.swap i j)
  rw [h, Perm.sign_swap hij] at h1
  ext γ
  have h2 := congrArg (fun y : Laurent d => y.coeff γ) h1
  simp only [coeff_single_zero_mul, Units.val_neg, Units.val_one, Int.reduceNeg, neg_mul,
    one_mul] at h2
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
  omega

/-- **The Pieri rule in alternant form**: for weakly decreasing `κ`,
`a_{κ+δ} · h_s = ∑ a_{κ+w+δ}`, over the exponent vectors `w` of `h_s` with `κ + w` interlacing
`κ`. -/
theorem alternant_mul_hsymm_pieri {κ : Weight d} (hκ : Antitone κ) (s : ℕ) :
    alternant (κ + staircase d) * toLaurent (MvPolynomial.hsymm (Fin d) ℤ s) =
      ∑ w ∈ pieriSet κ s, alternant (κ + liftW w + staircase d) := by
  rw [alternant_mul_hsymm]
  simp only [add_right_comm κ (staircase d)]
  rw [← Finset.sum_filter_add_sum_filter_not (compositionsOf d s) (fun w => ∀ i, ¬ Violates κ w i)]
  rw [pieriSet, add_eq_left]
  have hne : ∀ w ∈ (compositionsOf d s).filter (fun w => ¬ ∀ i, ¬ Violates κ w i),
      (Finset.univ.filter (Violates κ w)).Nonempty := by
    intro w hw
    have h := (Finset.mem_filter.mp hw).2
    push Not at h
    obtain ⟨i, hi⟩ := h
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  have htop : ∀ w hw, Violates κ w ((Finset.univ.filter (Violates κ w)).max' (hne w hw)) :=
    fun w hw => (Finset.mem_filter.mp (Finset.max'_mem _ (hne w hw))).2
  have hmem : ∀ w hw, swapW κ w ((Finset.univ.filter (Violates κ w)).max' (hne w hw)) ∈
      (compositionsOf d s).filter (fun w => ¬ ∀ i, ¬ Violates κ w i) := by
    intro w hw
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [mem_compositionsOf, sum_swapW hκ (htop w hw)]
      exact mem_compositionsOf.mp (Finset.mem_filter.mp hw).1
    · push Not
      exact ⟨_, violates_swapW hκ (htop w hw)⟩
  have hmax : ∀ w hw, (Finset.univ.filter (Violates κ
      (swapW κ w ((Finset.univ.filter (Violates κ w)).max' (hne w hw))))).max' (hne _ (hmem w hw)) =
        (Finset.univ.filter (Violates κ w)).max' (hne w hw) := by
    intro w hw
    set t := (Finset.univ.filter (Violates κ w)).max' (hne w hw)
    apply le_antisymm
    · apply Finset.max'_le
      intro k hk
      by_contra hlt
      push Not at hlt
      have hk' := (Finset.mem_filter.mp hk).2
      rw [violates_swapW_iff_of_lt hlt] at hk'
      exact absurd (Finset.le_max' _ k (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk'⟩))
        (not_le.mpr hlt)
    · exact Finset.le_max' _ t (Finset.mem_filter.mpr ⟨Finset.mem_univ t,
        violates_swapW hκ (htop w hw)⟩)
  refine Finset.sum_involution
    (fun w hw => swapW κ w ((Finset.univ.filter (Violates κ w)).max' (hne w hw)))
    (fun w hw => ?_) (fun w hw hf => ?_) hmem (fun w hw => ?_)
  · rw [add_swapW hκ (htop w hw), alternant_comp_perm,
      Perm.sign_swap (prev_ne (htop w hw).1)]
    simp only [Units.val_neg, Units.val_one, Int.reduceNeg]
    rw [show (AddMonoidAlgebra.single (0 : Weight d) (-1 : ℤ)) = -1 by
      rw [AddMonoidAlgebra.single_neg, ← AddMonoidAlgebra.one_def], neg_one_mul, add_neg_cancel]
  · intro heq
    apply hf
    apply alternant_eq_zero_of_comp_swap (prev_ne (htop w hw).1)
    rw [← add_swapW hκ (htop w hw), heq]
  · rw [hmax w hw]
    exact swapW_swapW hκ (htop w hw)

end

end Schubert.RS.Quiver.Schur
