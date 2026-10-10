import RSCounterexample.Paper.LR.RowCount

/-!
# The Littlewood–Richardson involution

Fix a weakly decreasing integer weight `κ` and a tableau `T` whose reverse row word is not lattice
from `κ`. Its **first violation** (`Schubert.RS.LR.IsFirstViolation`) is the least row `r` in
which the lattice condition fails, and the largest letter `i` failing there. Before row `r` the
balance `E = κ_i − κ_{i+1} + #i(rows < r) − #(i+1)(rows < r)` is nonnegative. Reading row `r`
from the right, the `(E + 1)`-st `i + 1` makes it negative; it sits in column `c₀ = b_r − E − 1`.

Write `a_k`, `n_k`, `b_k` for the numbers of entries `< i`, `≤ i` and `≤ i + 1` of row `k`.
The involution (`Schubert.RS.LR.lrSwap`) is Tau Ceti's `SemistandardYoungTableau.recut` at the
letter `i` with these splitting points (`Schubert.RS.LR.lrCut`):
- rows above `r`: their own;
- row `r`: the reflection of its own splitting point `n_r` in `[max(a_r, b_{r+1}), c₀]`;
- rows below `r`: the Bender–Knuth reflection.

The cells read up to the violation are left alone. On the cells read after it, the letters `i`
and `i + 1` are exchanged (`Schubert.RS.LR.content_lrSwap_add`).

The four conditions of `SemistandardYoungTableau.IsCut` hold row by row. The only nontrivial one
is at the boundary between rows `r − 1` and `r`: `c₀ < a_{r−1}` (`Schubert.RS.LR.cutCol_lt`, the
boundary lemma). It follows from `E ≥ #i(row r−1) = n_{r−1} − a_{r−1}` and
`b_r ≤ n_{r−1}` (strict columns).

## Main results

* `Schubert.RS.LR.exists_isFirstViolation`, `Schubert.RS.LR.IsFirstViolation.unique`.
* `Schubert.RS.LR.isFirstViolation_lrSwap`: the involution keeps the first violation.
* `Schubert.RS.LR.lrSwap_lrSwap`: it is an involution.
* `Schubert.RS.LR.content_lrSwap_add`, `Schubert.RS.LR.content_lrSwap_of_ne`: its effect on the
  content.
-/

namespace Schubert.RS.LR

noncomputable section

open SemistandardYoungTableau

variable {d : ℕ} {ν : YoungDiagram} {κ : Weight d} {T : _root_.SemistandardYoungTableau ν}
  {r i : ℕ}

theorem kap_succ_le (hκ : Antitone κ) {i : ℕ} (hi : i + 1 < d) : kap κ (i + 1) ≤ kap κ i := by
  rw [kap_of_lt κ hi, kap_of_lt κ (by omega)]
  exact hκ (Fin.mk_le_mk.mpr (Nat.le_succ i))

/-! ### The first violation -/

/-- `(r, i)` is the **first violation** of the lattice condition: the condition fails at row `r`
and letter `i`, holds at all earlier rows, and holds at row `r` for all larger letters. -/
structure IsFirstViolation (κ : Weight d) (T : _root_.SemistandardYoungTableau ν) (r i : ℕ) :
    Prop where
  lt : i + 1 < d
  viol : kap κ i + countBelow T r i < kap κ (i + 1) + countBelow T (r + 1) (i + 1)
  row_min : ∀ r' < r, ∀ j, j + 1 < d →
    kap κ (j + 1) + countBelow T (r' + 1) (j + 1) ≤ kap κ j + countBelow T r' j
  letter_max : ∀ j, i < j → j + 1 < d →
    kap κ (j + 1) + countBelow T (r + 1) (j + 1) ≤ kap κ j + countBelow T r j

theorem IsFirstViolation.not_isLattice (h : IsFirstViolation κ T r i) : ¬ IsLattice κ T :=
  fun hl => absurd (hl r i h.lt) (not_le.mpr h.viol)

/-- The first violation is unique. -/
theorem IsFirstViolation.unique {r' i' : ℕ} (h : IsFirstViolation κ T r i)
    (h' : IsFirstViolation κ T r' i') : r = r' ∧ i = i' := by
  have hr : r = r' := by
    rcases lt_trichotomy r r' with hlt | heq | hgt
    · exact absurd (h'.row_min r hlt i h.lt) (not_le.mpr h.viol)
    · exact heq
    · exact absurd (h.row_min r' hgt i' h'.lt) (not_le.mpr h'.viol)
  subst hr
  refine ⟨rfl, ?_⟩
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · exact absurd (h.letter_max i' hlt h'.lt) (not_le.mpr h'.viol)
  · exact heq
  · exact absurd (h'.letter_max i hgt h.lt) (not_le.mpr h.viol)

/-- A tableau that is not lattice has a first violation. -/
theorem exists_isFirstViolation (h : ¬ IsLattice κ T) : ∃ r i, IsFirstViolation κ T r i := by
  classical
  have hex : ∃ r, ∃ i, i + 1 < d ∧
      kap κ i + countBelow T r i < kap κ (i + 1) + countBelow T (r + 1) (i + 1) := by
    simp only [IsLattice, not_forall, not_le] at h
    obtain ⟨r, i, hi, hv⟩ := h
    exact ⟨r, i, hi, hv⟩
  obtain ⟨i₀, hi₀, hv₀⟩ := Nat.find_spec hex
  set S := (Finset.range d).filter fun i => i + 1 < d ∧
    kap κ i + countBelow T (Nat.find hex) i <
      kap κ (i + 1) + countBelow T (Nat.find hex + 1) (i + 1) with hSdef
  have hS : S.Nonempty := ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hi₀, hv₀⟩⟩
  have hi := Finset.mem_filter.mp (S.max'_mem hS)
  refine ⟨Nat.find hex, S.max' hS, ⟨hi.2.1, hi.2.2, fun r' hr' j hj => ?_, fun j hij hj => ?_⟩⟩
  · by_contra hc
    exact Nat.find_min hex hr' ⟨j, hj, not_le.mp hc⟩
  · by_contra hc
    have hjS : j ∈ S :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hj, not_le.mp hc⟩
    exact absurd (S.le_max' j hjS) (not_le.mpr hij)

/-! ### The balance before the violating row -/

/-- The balance between the letters `i` and `i + 1` before row `r`:
`κ_i − κ_{i+1} + #i(rows < r) − #(i+1)(rows < r)`. -/
def balance (κ : Weight d) (T : _root_.SemistandardYoungTableau ν) (r i : ℕ) : ℤ :=
  kap κ i - kap κ (i + 1) + countBelow T r i - countBelow T r (i + 1)

/-- After a row without violation, the balance is at least the number of `i`s of that row. -/
theorem rowCount_le_balance {k : ℕ} (h : IsFirstViolation κ T (k + 1) i) :
    (rowCount T k i : ℤ) ≤ balance κ T (k + 1) i := by
  have h1 := h.row_min k (Nat.lt_succ_self k) i h.lt
  rw [balance, countBelow_succ T k i]
  push_cast
  linarith

theorem balance_nonneg (hκ : Antitone κ) (h : IsFirstViolation κ T r i) :
    0 ≤ balance κ T r i := by
  cases r with
  | zero =>
    have := kap_succ_le hκ h.lt
    simp only [balance, countBelow_zero, Nat.cast_zero, add_zero, sub_zero]
    linarith
  | succ k => exact le_trans (Nat.cast_nonneg _) (rowCount_le_balance h)

theorem balance_lt_rowCount (h : IsFirstViolation κ T r i) :
    balance κ T r i < rowCount T r (i + 1) := by
  have h1 := h.viol
  rw [countBelow_succ T r (i + 1)] at h1
  rw [balance]
  push_cast at h1
  linarith

/-- The balance, as a natural number. -/
def eNat (κ : Weight d) (T : _root_.SemistandardYoungTableau ν) (r i : ℕ) : ℕ :=
  (balance κ T r i).toNat

theorem eNat_eq (hκ : Antitone κ) (h : IsFirstViolation κ T r i) :
    (eNat κ T r i : ℤ) = balance κ T r i :=
  Int.toNat_of_nonneg (balance_nonneg hκ h)

/-- The column of the violating cell: the `(E + 1)`-st `i + 1` of row `r`, from the right. -/
def cutCol (κ : Weight d) (T : _root_.SemistandardYoungTableau ν) (r i : ℕ) : ℕ :=
  rowCountLt T r (i + 2) - eNat κ T r i - 1

/-- The violating cell carries `i + 1`: it lies between the last `i` and the last `i + 1`. -/
theorem eNat_add_lt (hκ : Antitone κ) (h : IsFirstViolation κ T r i) :
    rowCountLt T r (i + 1) + eNat κ T r i + 1 ≤ rowCountLt T r (i + 2) := by
  have h1 := balance_lt_rowCount h
  rw [← eNat_eq hκ h] at h1
  have h2 : rowCountLt T r (i + 1) ≤ rowCountLt T r (i + 2) := T.rowCountLt_mono r (by omega)
  have h3 : (eNat κ T r i : ℤ) < (rowCountLt T r (i + 1 + 1) - rowCountLt T r (i + 1) : ℕ) := h1
  have h4 : eNat κ T r i < rowCountLt T r (i + 2) - rowCountLt T r (i + 1) := by exact_mod_cast h3
  omega

/-- **The boundary lemma**: the violating cell lies strictly left of the first
`i` of the row above, so no `i + 1` of row `r` up to the violating column sits below an `i`. -/
theorem cutCol_lt {k : ℕ} (hκ : Antitone κ) (h : IsFirstViolation κ T (k + 1) i) :
    cutCol κ T (k + 1) i + 1 ≤ rowCountLt T k i := by
  have h1 := rowCount_le_balance h
  rw [← eNat_eq hκ h] at h1
  have h2 : rowCount T k i ≤ eNat κ T (k + 1) i := by exact_mod_cast h1
  have h3 := eNat_add_lt hκ h
  have h4 : rowCountLt T (k + 1) (i + 2) ≤ rowCountLt T k (i + 1) := T.rowCountLt_succ_le k (i + 1)
  have h5 : rowCountLt T k i ≤ rowCountLt T k (i + 1) := T.rowCountLt_mono k (by omega)
  simp only [rowCount] at h2
  simp only [cutCol]
  omega

/-! ### The splitting points -/

/-- The lower end of the Bender–Knuth interval of row `k` at the letter `v`. -/
def lowerCut (T : _root_.SemistandardYoungTableau ν) (v k : ℕ) : ℕ :=
  max (rowCountLt T k v) (rowCountLt T (k + 1) (v + 2))

/-- The upper end of the Bender–Knuth interval of a row `k ≥ 1` at the letter `v`. -/
def upperCut (T : _root_.SemistandardYoungTableau ν) (v k : ℕ) : ℕ :=
  min (rowCountLt T k (v + 2)) (rowCountLt T (k - 1) v)

/-- **The splitting points of the involution**: the own ones above row `r`, the reflection in
`[max(a_r, b_{r+1}), c₀]` in row `r`, and the Bender–Knuth reflection below. -/
def lrCut (κ : Weight d) (T : _root_.SemistandardYoungTableau ν) (r i k : ℕ) : ℕ :=
  if k < r then rowCountLt T k (i + 1)
  else if k = r then lowerCut T i r + cutCol κ T r i - rowCountLt T r (i + 1)
  else lowerCut T i k + upperCut T i k - rowCountLt T k (i + 1)

/-- The row-count inequalities of a semistandard tableau used throughout. -/
theorem row_facts (T : _root_.SemistandardYoungTableau ν) (i k : ℕ) :
    rowCountLt T k i ≤ rowCountLt T k (i + 1) ∧ rowCountLt T k (i + 1) ≤ rowCountLt T k (i + 2) ∧
      rowCountLt T (k + 1) (i + 2) ≤ rowCountLt T k (i + 1) ∧
      rowCountLt T (k + 1) (i + 1) ≤ rowCountLt T k i :=
  ⟨T.rowCountLt_mono k (by omega), T.rowCountLt_mono k (by omega), T.rowCountLt_succ_le k (i + 1),
    T.rowCountLt_succ_le k i⟩

theorem lrCut_of_lt {k : ℕ} (hk : k < r) : lrCut κ T r i k = rowCountLt T k (i + 1) := by
  simp [lrCut, hk]

theorem lrCut_self : lrCut κ T r i r =
    lowerCut T i r + cutCol κ T r i - rowCountLt T r (i + 1) := by
  simp [lrCut]

theorem lrCut_of_gt {k : ℕ} (hk : r < k) :
    lrCut κ T r i k = lowerCut T i k + upperCut T i k - rowCountLt T k (i + 1) := by
  simp [lrCut, not_lt.mpr hk.le, hk.ne']

/-- Below the violating row, the Bender–Knuth interval contains the own splitting point. -/
theorem lowerCut_le_le_upperCut (T : _root_.SemistandardYoungTableau ν) (i : ℕ) {k : ℕ}
    (hk : 1 ≤ k) :
    lowerCut T i k ≤ rowCountLt T k (i + 1) ∧ rowCountLt T k (i + 1) ≤ upperCut T i k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  obtain ⟨h1, h2, h3, h4⟩ := row_facts T i (m + 1)
  obtain ⟨_, _, _, h8⟩ := row_facts T i m
  simp only [lowerCut, upperCut, Nat.add_sub_cancel]
  omega

/-- **The splitting points of the involution are admissible.** -/
theorem isCut_lrCut (hκ : Antitone κ) (h : IsFirstViolation κ T r i) :
    IsCut T i (lrCut κ T r i) := by
  have hr := eNat_add_lt hκ h
  have hr' : lowerCut T i r ≤ rowCountLt T r (i + 1) := by
    obtain ⟨h1, -, h3, -⟩ := row_facts T i r
    simp only [lowerCut]
    omega
  have hc : rowCountLt T r (i + 1) ≤ cutCol κ T r i ∧ cutCol κ T r i < rowCountLt T r (i + 2) := by
    simp only [cutCol]
    omega
  refine ⟨fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := row_facts T i k
    rcases lt_trichotomy k r with hk | rfl | hk
    · rw [lrCut_of_lt hk]
      exact h1
    · rw [lrCut_self]
      simp only [lowerCut] at hr' ⊢
      omega
    · rw [lrCut_of_gt hk]
      have := lowerCut_le_le_upperCut T i (k := k) (by omega)
      simp only [lowerCut] at this ⊢
      omega
  · obtain ⟨h1, h2, h3, h4⟩ := row_facts T i k
    rcases lt_trichotomy k r with hk | rfl | hk
    · rw [lrCut_of_lt hk]
      exact h2
    · rw [lrCut_self]
      omega
    · rw [lrCut_of_gt hk]
      have := lowerCut_le_le_upperCut T i (k := k) (by omega)
      have hU : upperCut T i k ≤ rowCountLt T k (i + 2) := min_le_left _ _
      omega
  · obtain ⟨h1, h2, h3, h4⟩ := row_facts T i k
    rcases lt_trichotomy k r with hk | rfl | hk
    · rw [lrCut_of_lt hk]
      exact h3
    · rw [lrCut_self]
      simp only [lowerCut] at hr' ⊢
      omega
    · rw [lrCut_of_gt hk]
      have := lowerCut_le_le_upperCut T i (k := k) (by omega)
      have hL : rowCountLt T (k + 1) (i + 2) ≤ lowerCut T i k := le_max_right _ _
      omega
  · obtain ⟨h1, h2, h3, h4⟩ := row_facts T i k
    rcases lt_trichotomy (k + 1) r with hk | hk | hk
    · rw [lrCut_of_lt hk]
      exact h4
    · subst hk
      rw [lrCut_self]
      have hkey := cutCol_lt hκ h
      omega
    · rw [lrCut_of_gt hk]
      have := lowerCut_le_le_upperCut T i (k := k + 1) (by omega)
      have hU : upperCut T i (k + 1) ≤ rowCountLt T k i := by
        simp only [upperCut, Nat.add_sub_cancel]
        exact min_le_right _ _
      omega

/-! ### The involution -/

/-- **The Littlewood–Richardson involution**: the recut of `T` at the letter `i` with the splitting
points `Schubert.RS.LR.lrCut`. -/
def lrSwap (hκ : Antitone κ) (h : IsFirstViolation κ T r i) : _root_.SemistandardYoungTableau ν :=
  recut T i (lrCut κ T r i) (isCut_lrCut hκ h)

theorem rowCountLt_lrSwap_of_ne (hκ : Antitone κ) (h : IsFirstViolation κ T r i) (k : ℕ)
    {x : ℕ} (hx : x ≠ i + 1) : rowCountLt (lrSwap hκ h) k x = rowCountLt T k x := by
  rcases le_or_gt x i with hxi | hxi
  · exact rowCountLt_recut_of_le _ k hxi
  · exact rowCountLt_recut_of_ge _ k (by omega)

theorem rowCountLt_lrSwap_succ (hκ : Antitone κ) (h : IsFirstViolation κ T r i) (k : ℕ) :
    rowCountLt (lrSwap hκ h) k (i + 1) = lrCut κ T r i k :=
  rowCountLt_recut_succ _ k

/-- Above the violating row, nothing changes. -/
theorem rowCountLt_lrSwap_of_lt (hκ : Antitone κ) (h : IsFirstViolation κ T r i) {k : ℕ}
    (hk : k < r) (x : ℕ) : rowCountLt (lrSwap hκ h) k x = rowCountLt T k x := by
  by_cases hx : x = i + 1
  · subst hx
    rw [rowCountLt_lrSwap_succ, lrCut_of_lt hk]
  · exact rowCountLt_lrSwap_of_ne hκ h k hx

theorem rowCount_lrSwap (hκ : Antitone κ) (h : IsFirstViolation κ T r i) (k x : ℕ)
    (hkx : k < r ∨ (x ≠ i ∧ x ≠ i + 1)) : rowCount (lrSwap hκ h) k x = rowCount T k x := by
  rcases hkx with hk | ⟨hx, hx'⟩
  · simp only [rowCount, rowCountLt_lrSwap_of_lt hκ h hk]
  · simp only [rowCount]
    rw [rowCountLt_lrSwap_of_ne hκ h k (by omega), rowCountLt_lrSwap_of_ne hκ h k hx']

theorem countBelow_lrSwap (hκ : Antitone κ) (h : IsFirstViolation κ T r i) (R x : ℕ)
    (hRx : R ≤ r ∨ (x ≠ i ∧ x ≠ i + 1)) : countBelow (lrSwap hκ h) R x = countBelow T R x := by
  refine Finset.sum_congr rfl fun k hk => rowCount_lrSwap hκ h k x ?_
  rcases hRx with hR | hx
  · exact Or.inl (lt_of_lt_of_le (Finset.mem_range.mp hk) hR)
  · exact Or.inr hx

theorem lrCut_self_le (hκ : Antitone κ) (h : IsFirstViolation κ T r i) :
    lrCut κ T r i r ≤ cutCol κ T r i := by
  have hr := eNat_add_lt hκ h
  obtain ⟨h1, -, h3, -⟩ := row_facts T i r
  rw [lrCut_self]
  simp only [lowerCut, cutCol] at *
  omega

/-- **The involution keeps the first violation.** -/
theorem isFirstViolation_lrSwap (hκ : Antitone κ) (h : IsFirstViolation κ T r i) :
    IsFirstViolation κ (lrSwap hκ h) r i where
  lt := h.lt
  viol := by
    have hb := balance_lt_rowCount h
    have hcut := lrCut_self_le hκ h
    have hr := eNat_add_lt hκ h
    have he := eNat_eq hκ h
    rw [countBelow_lrSwap hκ h r i (Or.inl le_rfl), countBelow_succ,
      countBelow_lrSwap hκ h r (i + 1) (Or.inl le_rfl)]
    have hrc : rowCount (lrSwap hκ h) r (i + 1) = rowCountLt T r (i + 2) - lrCut κ T r i r := by
      simp only [rowCount]
      rw [rowCountLt_lrSwap_of_ne hκ h r (by omega), rowCountLt_lrSwap_succ]
    have hlt : eNat κ T r i < rowCount (lrSwap hκ h) r (i + 1) := by
      rw [hrc]
      simp only [cutCol] at hcut
      omega
    have hlt' : (eNat κ T r i : ℤ) < rowCount (lrSwap hκ h) r (i + 1) := by exact_mod_cast hlt
    rw [he, balance] at hlt'
    push_cast
    linarith
  row_min r' hr' j hj := by
    rw [countBelow_lrSwap hκ h (r' + 1) (j + 1) (Or.inl hr'),
      countBelow_lrSwap hκ h r' j (Or.inl hr'.le)]
    exact h.row_min r' hr' j hj
  letter_max j hij hj := by
    rw [countBelow_lrSwap hκ h (r + 1) (j + 1) (Or.inr ⟨by omega, by omega⟩),
      countBelow_lrSwap hκ h r j (Or.inl le_rfl)]
    exact h.letter_max j hij hj

theorem balance_lrSwap (hκ : Antitone κ) (h : IsFirstViolation κ T r i) :
    balance κ (lrSwap hκ h) r i = balance κ T r i := by
  simp only [balance, countBelow_lrSwap hκ h r _ (Or.inl le_rfl)]

theorem cutCol_lrSwap (hκ : Antitone κ) (h : IsFirstViolation κ T r i) :
    cutCol κ (lrSwap hκ h) r i = cutCol κ T r i := by
  simp only [cutCol, eNat, balance_lrSwap hκ h, rowCountLt_lrSwap_of_ne hκ h r (by omega :
    i + 2 ≠ i + 1)]

theorem lowerCut_lrSwap (hκ : Antitone κ) (h : IsFirstViolation κ T r i) (k : ℕ) :
    lowerCut (lrSwap hκ h) i k = lowerCut T i k := by
  simp only [lowerCut, rowCountLt_lrSwap_of_ne hκ h _ (by omega : i ≠ i + 1),
    rowCountLt_lrSwap_of_ne hκ h _ (by omega : i + 2 ≠ i + 1)]

theorem upperCut_lrSwap (hκ : Antitone κ) (h : IsFirstViolation κ T r i) (k : ℕ) :
    upperCut (lrSwap hκ h) i k = upperCut T i k := by
  simp only [upperCut, rowCountLt_lrSwap_of_ne hκ h _ (by omega : i ≠ i + 1),
    rowCountLt_lrSwap_of_ne hκ h _ (by omega : i + 2 ≠ i + 1)]

/-- The splitting points of the involution, computed on the image, are the own ones of `T`. -/
theorem lrCut_lrSwap (hκ : Antitone κ) (h : IsFirstViolation κ T r i) :
    lrCut κ (lrSwap hκ h) r i = fun k => rowCountLt T k (i + 1) := by
  funext k
  rcases lt_trichotomy k r with hk | rfl | hk
  · rw [lrCut_of_lt hk, rowCountLt_lrSwap_succ, lrCut_of_lt hk]
  · have hr := eNat_add_lt hκ h
    obtain ⟨h1, -, h3, -⟩ := row_facts T i k
    rw [lrCut_self, lowerCut_lrSwap, cutCol_lrSwap, rowCountLt_lrSwap_succ, lrCut_self]
    simp only [lowerCut, cutCol] at *
    omega
  · have := lowerCut_le_le_upperCut T i (k := k) (by omega)
    rw [lrCut_of_gt hk, lowerCut_lrSwap, upperCut_lrSwap, rowCountLt_lrSwap_succ, lrCut_of_gt hk]
    omega

theorem recut_congr {v : ℕ} {cut cut' : ℕ → ℕ} (hc : IsCut T v cut) (hc' : IsCut T v cut')
    (h : cut = cut') : recut T v cut hc = recut T v cut' hc' := by
  subst h
  rfl

/-- **The involution is an involution.** -/
theorem lrSwap_lrSwap (hκ : Antitone κ) (h : IsFirstViolation κ T r i) :
    lrSwap hκ (isFirstViolation_lrSwap hκ h) = T := by
  have hcut := isCut_lrCut hκ h
  have hown := isCut_rowCountLt T i
  calc lrSwap hκ (isFirstViolation_lrSwap hκ h)
      = recut (recut T i (lrCut κ T r i) hcut) i (fun k => rowCountLt T k (i + 1))
          (hcut.recut hown) :=
        recut_congr _ _ (lrCut_lrSwap hκ h)
    _ = recut T i (fun k => rowCountLt T k (i + 1)) hown := recut_recut hcut hown
    _ = T := recut_rowCountLt T i

/-! ### The effect on the content -/

/-- The violating row is a row of the shape. -/
theorem lt_colLen (hκ : Antitone κ) (h : IsFirstViolation κ T r i) : r < ν.colLen 0 := by
  by_contra hc
  have := eNat_add_lt hκ h
  simp only [rowCountLt_eq_zero_of_colLen_le T (not_lt.mp hc)] at this
  omega

theorem content_lrSwap_of_ne (hκ : Antitone κ) (h : IsFirstViolation κ T r i) {x : ℕ}
    (hx : x ≠ i) (hx' : x ≠ i + 1) : content (lrSwap hκ h) x = content T x :=
  content_recut_of_ne _ hx hx'

theorem content_lrSwap_pair (hκ : Antitone κ) (h : IsFirstViolation κ T r i) :
    content (lrSwap hκ h) i + content (lrSwap hκ h) (i + 1) = content T i + content T (i + 1) :=
  content_recut_add _

/-- The telescoping identity of the Bender–Knuth reflection below the violating row. -/
theorem sum_Ico_lrCut (κ : Weight d) (T : _root_.SemistandardYoungTableau ν) (r i m : ℕ) :
    ∑ k ∈ Finset.Ico (r + 1) (r + 1 + m), (lrCut κ T r i k - rowCountLt T k i) +
        (rowCountLt T (r + 1) (i + 2) - upperCut T i (r + 1)) =
      (rowCountLt T (r + 1 + m) (i + 2) - upperCut T i (r + 1 + m)) +
        ∑ k ∈ Finset.Ico (r + 1) (r + 1 + m),
          (rowCountLt T k (i + 2) - rowCountLt T k (i + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show r + 1 + (m + 1) = r + 1 + m + 1 by omega, Finset.sum_Ico_succ_top (by omega),
      Finset.sum_Ico_succ_top (by omega)]
    have hk : r < r + 1 + m := by omega
    have hfac := lowerCut_le_le_upperCut T i (k := r + 1 + m) (by omega)
    have hUb : upperCut T i (r + 1 + m) ≤ rowCountLt T (r + 1 + m) (i + 2) := min_le_left _ _
    obtain ⟨h1, h2, h3, h4⟩ := row_facts T i (r + 1 + m)
    have hU : upperCut T i (r + 1 + m + 1) =
        min (rowCountLt T (r + 1 + m + 1) (i + 2)) (rowCountLt T (r + 1 + m) i) := by
      simp [upperCut]
    rw [lrCut_of_gt hk, hU]
    simp only [lowerCut] at hfac ⊢
    omega

/-- **The involution exchanges the letters `i` and `i + 1` on the cells read after the violation**:
`#i(T*) = #(i+1)(T) + κ_{i+1} − κ_i − 1`, in the additive form
`#i(T*) + E + 1 + #(i+1)(rows < r) = #(i+1)(T) + #i(rows < r)`. -/
theorem content_lrSwap_add (hκ : Antitone κ) (h : IsFirstViolation κ T r i) :
    content (lrSwap hκ h) i + eNat κ T r i + 1 + countBelow T r (i + 1) =
      content T (i + 1) + countBelow T r i := by
  have hM := lt_colLen hκ h
  set M := ν.colLen 0 with hMdef
  have h1 : content (lrSwap hκ h) i = ∑ k ∈ Finset.range M, (lrCut κ T r i k - rowCountLt T k i) :=
    content_recut _
  have h2 : content T (i + 1) =
      ∑ k ∈ Finset.range M, (rowCountLt T k (i + 2) - rowCountLt T k (i + 1)) :=
    content_succ_eq_sum T i
  have hsplit : ∀ f : ℕ → ℕ, ∑ k ∈ Finset.range M, f k =
      ∑ k ∈ Finset.range r, f k + f r + ∑ k ∈ Finset.Ico (r + 1) (r + 1 + (M - (r + 1))), f k := by
    intro f
    have hM' : r + 1 + (M - (r + 1)) = M := by omega
    rw [hM', Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive f (Nat.zero_le r) hM.le,
      Finset.sum_eq_sum_Ico_succ_bot hM, ← add_assoc, Finset.range_eq_Ico]
  have htel := sum_Ico_lrCut κ T r i (M - (r + 1))
  have hzero : rowCountLt T (r + 1 + (M - (r + 1))) (i + 2) = 0 :=
    rowCountLt_eq_zero_of_colLen_le T (by omega) _
  have habove : ∑ k ∈ Finset.range r, (lrCut κ T r i k - rowCountLt T k i) = countBelow T r i :=
    Finset.sum_congr rfl fun k hk => by rw [lrCut_of_lt (Finset.mem_range.mp hk)]; rfl
  have habove' : ∑ k ∈ Finset.range r, (rowCountLt T k (i + 2) - rowCountLt T k (i + 1)) =
      countBelow T r (i + 1) := rfl
  have hr := eNat_add_lt hκ h
  obtain ⟨g1, g2, g3, g4⟩ := row_facts T i r
  have hrow : lrCut κ T r i r - rowCountLt T r i =
      (rowCountLt T (r + 1) (i + 2) - upperCut T i (r + 1)) +
        (cutCol κ T r i - rowCountLt T r (i + 1)) := by
    rw [lrCut_self]
    simp only [lowerCut, upperCut, cutCol, Nat.add_sub_cancel]
    omega
  rw [h1, h2, hsplit, hsplit, habove, habove', hrow]
  rw [hzero, Nat.zero_sub, zero_add] at htel
  simp only [cutCol] at *
  omega

end

end Schubert.RS.LR
