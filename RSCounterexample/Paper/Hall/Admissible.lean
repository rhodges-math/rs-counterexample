import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Finset.Max

/-!
# Hall-admissible subsets and canonical flags

Fix integers `0 ≤ ℓ_1 ≤ ⋯ ≤ ℓ_m`. A subset `{j_1 < ⋯ < j_d}` of `{1, …, m}` is *Hall
admissible* if `ℓ_{j_k} ≥ k` for every `k` (Section 3.1 of the paper). Lemma 3.8 of the paper
(`lem:hall-flags`) describes these subsets by strictly increasing lower bounds, the canonical
flags `f_0 = 0`, `f_k = max(min{j : ℓ_j ≥ k}, f_{k−1} + 1)` ((3.7), eq:canonical-flags), an empty
minimum being `m + 1`: a subset is Hall admissible if and only if `j_k ≥ f_k` for every `k`.

Positions are `0`-based in Lean: a subset is a strictly increasing `J : Fin d → Fin m`, with
`j_k = J (k − 1) + 1`. The flags keep the paper's `1`-based values.

## Main definitions

* `Schubert.RS.Hall.IsHallAdmissible ℓ J`: the subset listed by `J` is Hall admissible.
* `Schubert.RS.Hall.firstAbove ℓ k`: `min{j : ℓ_j ≥ k}` (`1`-based), or `m + 1`.
* `Schubert.RS.Hall.hallFlag ℓ k`: the canonical flag `f_k`.

## Main results

* `Schubert.RS.Hall.hall_flags` (`lem:hall-flags`).
-/

namespace Schubert.RS.Hall

variable {d m : ℕ}

/-- The subset `{J 0 < ⋯ < J (d − 1)}` of `{0, …, m − 1}` is Hall admissible for the heights `ℓ`:
in the paper's `1`-based indexing, `ℓ_{j_k} ≥ k` for every `k`. -/
def IsHallAdmissible (ℓ : Fin m → ℕ) (J : Fin d → Fin m) : Prop :=
  StrictMono J ∧ ∀ k : Fin d, k.val + 1 ≤ ℓ (J k)

instance (ℓ : Fin m → ℕ) : DecidablePred (IsHallAdmissible (d := d) ℓ) := fun J => by
  unfold IsHallAdmissible StrictMono
  infer_instance

open Classical in
/-- `min{j : ℓ_j ≥ k}` in the paper's `1`-based indexing, the empty minimum being `m + 1`. -/
noncomputable def firstAbove (ℓ : Fin m → ℕ) (k : ℕ) : ℕ :=
  if h : ∃ j : Fin m, k ≤ ℓ j then
    ((Finset.univ.filter fun j : Fin m => k ≤ ℓ j).min'
      (let ⟨j, hj⟩ := h; ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩)).val + 1
  else m + 1

/-- The canonical flags ((3.7), eq:canonical-flags): `f_0 = 0` and
`f_k = max(min{j : ℓ_j ≥ k}, f_{k−1} + 1)`. -/
noncomputable def hallFlag (ℓ : Fin m → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => max (firstAbove ℓ (k + 1)) (hallFlag ℓ k + 1)

/-- For weakly increasing heights, `j ≥ min{j' : ℓ_{j'} ≥ k}` exactly when `ℓ_j ≥ k`. -/
theorem firstAbove_le_iff (ℓ : Fin m → ℕ) (hℓ : Monotone ℓ) (k : ℕ) (j : Fin m) :
    firstAbove ℓ k ≤ j.val + 1 ↔ k ≤ ℓ j := by
  classical
  unfold firstAbove
  split_ifs with h
  · constructor
    · intro hle
      have hmin := Finset.min'_mem (Finset.univ.filter fun j : Fin m => k ≤ ℓ j)
        (let ⟨j, hj⟩ := h; ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩)
      have h1 := (Finset.mem_filter.mp hmin).2
      have h2 : (Finset.univ.filter fun j : Fin m => k ≤ ℓ j).min'
          (let ⟨j, hj⟩ := h; ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩) ≤ j :=
        Fin.le_def.mpr (by omega)
      exact h1.trans (hℓ h2)
    · intro hk
      have := Finset.min'_le (Finset.univ.filter fun j : Fin m => k ≤ ℓ j) j
        (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hk⟩)
      have : ((Finset.univ.filter fun j : Fin m => k ≤ ℓ j).min'
          (let ⟨j, hj⟩ := h; ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩)).val ≤ j.val :=
        Fin.le_def.mp this
      omega
  · constructor
    · intro hle
      have := j.isLt
      omega
    · intro hk
      exact absurd ⟨j, hk⟩ h

theorem firstAbove_le_hallFlag (ℓ : Fin m → ℕ) (k : ℕ) :
    firstAbove ℓ (k + 1) ≤ hallFlag ℓ (k + 1) :=
  le_max_left _ _

/-- **Lemma 3.8 of the paper** (`lem:hall-flags`). For weakly increasing heights, a subset
`{j_1 < ⋯ < j_d}` is Hall admissible if and only if `j_k ≥ f_k` for every `k`. -/
theorem hall_flags (ℓ : Fin m → ℕ) (hℓ : Monotone ℓ) (J : Fin d → Fin m) (hJ : StrictMono J) :
    (∀ k : Fin d, k.val + 1 ≤ ℓ (J k)) ↔ ∀ k : Fin d, hallFlag ℓ (k.val + 1) ≤ (J k).val + 1 := by
  constructor
  · intro h
    have key : ∀ k (hk : k < d), hallFlag ℓ (k + 1) ≤ (J ⟨k, hk⟩).val + 1 := by
      intro k
      induction k with
      | zero =>
        intro hk
        have h1 := (firstAbove_le_iff ℓ hℓ 1 (J ⟨0, hk⟩)).mpr (h ⟨0, hk⟩)
        show max (firstAbove ℓ 1) (hallFlag ℓ 0 + 1) ≤ _
        simp only [hallFlag, zero_add]
        exact max_le h1 (by omega)
      | succ k ih =>
        intro hk
        have h1 := (firstAbove_le_iff ℓ hℓ (k + 2) (J ⟨k + 1, hk⟩)).mpr (h ⟨k + 1, hk⟩)
        have h2 := ih (by omega)
        have h3 : (J ⟨k, by omega⟩).val < (J ⟨k + 1, hk⟩).val :=
          hJ (Fin.mk_lt_mk.mpr (Nat.lt_succ_self k))
        show max (firstAbove ℓ (k + 2)) (hallFlag ℓ (k + 1) + 1) ≤ _
        exact max_le h1 (by omega)
    exact fun k => key k.val k.isLt
  · intro h k
    exact (firstAbove_le_iff ℓ hℓ (k.val + 1) (J k)).mp
      ((firstAbove_le_hallFlag ℓ k.val).trans (h k))

/-- Hall admissibility in terms of the canonical flags. -/
theorem isHallAdmissible_iff_flags (ℓ : Fin m → ℕ) (hℓ : Monotone ℓ) (J : Fin d → Fin m) :
    IsHallAdmissible ℓ J ↔ StrictMono J ∧ ∀ k : Fin d, hallFlag ℓ (k.val + 1) ≤ (J k).val + 1 := by
  constructor
  · rintro ⟨hJ, h⟩
    exact ⟨hJ, (hall_flags ℓ hℓ J hJ).mp h⟩
  · rintro ⟨hJ, h⟩
    exact ⟨hJ, (hall_flags ℓ hℓ J hJ).mpr h⟩

end Schubert.RS.Hall
