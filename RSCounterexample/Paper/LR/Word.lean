import RSCounterexample.Paper.LR.Rule

/-!
# The reverse row word

The reverse row word of a tableau reads its rows top to bottom, each right to left. It is lattice
from `κ` when `κ` plus the content of every prefix is weakly decreasing
(`Schubert.RS.LR.IsLatticeFrom`). This file proves that this is the row-count condition
`Schubert.RS.LR.IsLattice` (`Schubert.RS.LR.isLatticeFrom_iff`), and states the
Littlewood–Richardson rule in reading-word form, counting the tableaux whose reverse row word is
lattice from `κ` (`Schubert.RS.LR.alternant_mul_schur_word`).

A prefix of the word is made of the full rows `0, …, R − 1` and the last `m` entries of row `R`.
Rows increase weakly, so the entries `x` among the last `m` cells of row `R` are those in the
columns `[max(L − m, a_x), a_{x+1})`, where `L` is the length of the row and `a_y` counts its
entries `< y` (`Schubert.RS.LR.count_take_rowWord`). Within row `R`, the balance between the
letters `i` and `i + 1` is lowest once the `(i + 1)`s are read and before the `i`s, which is the
inequality of `IsLattice` at row `R`.
-/

namespace Schubert.RS.LR

noncomputable section

open SemistandardYoungTableau Schubert.RS.Quiver.Schur

variable {d : ℕ} {ν : YoungDiagram}

/-! ### The words -/

/-- The word of row `r`, read right to left. -/
def rowWord (T : _root_.SemistandardYoungTableau ν) (r : ℕ) : List ℕ :=
  (List.range (ν.rowLen r)).reverse.map fun c => T r c

/-- The words of the rows `0, …, R − 1`, concatenated. -/
def rowsWord (T : _root_.SemistandardYoungTableau ν) : ℕ → List ℕ
  | 0 => []
  | R + 1 => rowsWord T R ++ rowWord T R

/-- **The reverse row word**: the rows top to bottom, each right to left. -/
def reverseRowWord (T : _root_.SemistandardYoungTableau ν) : List ℕ :=
  rowsWord T (ν.colLen 0)

/-- **A word is lattice from `κ`** when `κ` plus the content of every prefix is weakly
decreasing. -/
def IsLatticeFrom (κ : Weight d) (w : List ℕ) : Prop :=
  ∀ k ≤ w.length, Antitone (κ + fun i : Fin d => ((w.take k).count i.val : ℤ))

theorem length_rowWord (T : _root_.SemistandardYoungTableau ν) (r : ℕ) :
    (rowWord T r).length = ν.rowLen r := by
  simp [rowWord]

/-- **The last `m` entries of a row**: the `x`s among them sit in the columns
`[max(L − m, a_x), a_{x+1})`. -/
theorem count_take_rowWord (T : _root_.SemistandardYoungTableau ν) (r x : ℕ) {m : ℕ}
    (hm : m ≤ ν.rowLen r) :
    ((rowWord T r).take m).count x =
      rowCountLt T r (x + 1) - max (ν.rowLen r - m) (rowCountLt T r x) := by
  induction m with
  | zero =>
    have h1 := T.rowCountLt_le_rowLen r (x + 1)
    simp only [List.take_zero, List.count_nil, Nat.sub_zero]
    omega
  | succ m ih =>
    have hm' : m < ν.rowLen r := by omega
    have hget : (rowWord T r)[m]? = some (T r (ν.rowLen r - 1 - m)) := by
      rw [rowWord, List.getElem?_map, List.getElem?_reverse (by simpa using hm'),
        List.length_range, List.getElem?_range (by omega)]
      rfl
    rw [List.take_add_one, hget, Option.toList_some, List.count_append, ih (by omega),
      List.count_singleton]
    simp only [beq_iff_eq]
    have hcL : ν.rowLen r - 1 - m < ν.rowLen r := by omega
    have h1 := T.lt_rowCountLt_iff (x := x) hcL
    have h2 := T.lt_rowCountLt_iff (x := x + 1) hcL
    have h3 : rowCountLt T r x ≤ rowCountLt T r (x + 1) := T.rowCountLt_mono r (by omega)
    have h4 := T.rowCountLt_le_rowLen r (x + 1)
    by_cases he : T r (ν.rowLen r - 1 - m) = x
    · have hca : ¬ (ν.rowLen r - 1 - m < rowCountLt T r x) := fun hh => by
        have := h1.mp hh
        omega
      have hcn : ν.rowLen r - 1 - m < rowCountLt T r (x + 1) := h2.mpr (by omega)
      rw [ite_eq_left he]
      omega
    · have key : ν.rowLen r - 1 - m < rowCountLt T r x ∨
          ¬ (ν.rowLen r - 1 - m < rowCountLt T r (x + 1)) := by
        rcases lt_or_gt_of_ne he with hlt | hgt
        · exact Or.inl (h1.mpr hlt)
        · exact Or.inr fun hh => by
            have := h2.mp hh
            omega
      rw [ite_eq_right he]
      omega

theorem count_rowWord (T : _root_.SemistandardYoungTableau ν) (r x : ℕ) :
    (rowWord T r).count x = rowCount T r x := by
  have h := count_take_rowWord T r x (le_refl (ν.rowLen r))
  rw [List.take_of_length_le (le_of_eq (length_rowWord T r))] at h
  rw [h, rowCount, Nat.sub_self, Nat.zero_max]

theorem count_rowsWord (T : _root_.SemistandardYoungTableau ν) (R x : ℕ) :
    (rowsWord T R).count x = countBelow T R x := by
  induction R with
  | zero => simp [rowsWord]
  | succ R ih => rw [rowsWord, List.count_append, ih, count_rowWord, countBelow_succ]

theorem length_rowsWord_mono (T : _root_.SemistandardYoungTableau ν) {R R' : ℕ} (h : R ≤ R') :
    (rowsWord T R).length ≤ (rowsWord T R').length := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction m with
  | zero => exact le_rfl
  | succ m ih => exact ih.trans (by simp [rowsWord])

theorem rowsWord_append (T : _root_.SemistandardYoungTableau ν) {R R' : ℕ} (h : R ≤ R') :
    ∃ l, rowsWord T R' = rowsWord T R ++ l := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  induction m with
  | zero => exact ⟨[], by simp⟩
  | succ m ih =>
    obtain ⟨l, hl⟩ := ih (Nat.le_add_right _ _)
    exact ⟨l ++ rowWord T (R + m), by rw [← add_assoc, rowsWord, hl, List.append_assoc]⟩

/-- The prefixes of `rowsWord T R'` of length at most that of `rowsWord T R` are prefixes of
`rowsWord T R`. -/
theorem take_rowsWord (T : _root_.SemistandardYoungTableau ν) {R R' k : ℕ} (h : R ≤ R')
    (hk : k ≤ (rowsWord T R).length) : (rowsWord T R').take k = (rowsWord T R).take k := by
  obtain ⟨l, hl⟩ := rowsWord_append T h
  rw [hl, List.take_append_of_le_length hk]

/-! ### The equivalence with the row-count form -/

/-- A function on `Fin d` is weakly decreasing as soon as it decreases at every step. -/
theorem antitone_of_succ {f : Fin d → ℤ}
    (h : ∀ i : ℕ, ∀ hi : i + 1 < d, f ⟨i + 1, hi⟩ ≤ f ⟨i, by omega⟩) : Antitone f := by
  intro a b hab
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  simp only [Fin.mk_le_mk] at hab
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction m with
  | zero => exact le_rfl
  | succ m ih => exact (h (a + m) (by omega)).trans (ih (by omega) (by omega))

/-- The prefixes of the row words, row by row, are lattice when `T` is. -/
theorem isLatticeFrom_rowsWord {κ : Weight d} {T : _root_.SemistandardYoungTableau ν}
    (h : IsLattice κ T) (R : ℕ) : IsLatticeFrom κ (rowsWord T R) := by
  induction R with
  | zero =>
    intro k _
    refine antitone_of_succ fun i hi => ?_
    have h0 := h 0 i hi
    have hn : (0 : ℤ) ≤ countBelow T 1 (i + 1) := Nat.cast_nonneg _
    rw [kap_of_lt κ hi, kap_of_lt κ (by omega), countBelow_zero] at h0
    simp only [rowsWord, List.take_nil, List.count_nil, Nat.cast_zero, Pi.add_apply, add_zero]
    push_cast at h0
    linarith
  | succ R ih =>
    intro k hk
    by_cases hkR : k ≤ (rowsWord T R).length
    · have := ih k hkR
      rwa [rowsWord, List.take_append_of_le_length hkR]
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (le_of_not_ge hkR)
      have hm : m ≤ ν.rowLen R := by
        simp only [rowsWord, List.length_append, length_rowWord] at hk
        omega
      rw [rowsWord, List.take_length_add_append]
      refine antitone_of_succ fun i hi => ?_
      have h1 := h R i hi
      rw [kap_of_lt κ hi, kap_of_lt κ (by omega), countBelow_succ] at h1
      simp only [Pi.add_apply, List.count_append, count_rowsWord, count_take_rowWord T R _ hm]
      have g1 := T.rowCountLt_mono R (Nat.le_succ i)
      have g2 := T.rowCountLt_mono R (Nat.le_succ (i + 1))
      have hle : rowCountLt T R (i + 1 + 1) - max (ν.rowLen R - m) (rowCountLt T R (i + 1)) ≤
          rowCount T R (i + 1) := by
        simp only [rowCount]
        omega
      have hle' : (↑(rowCountLt T R (i + 1 + 1) - max (ν.rowLen R - m) (rowCountLt T R (i + 1)))
          : ℤ) ≤ rowCount T R (i + 1) := by exact_mod_cast hle
      push_cast at h1 ⊢
      have hn : (0 : ℤ) ≤ ((rowCountLt T R (i + 1) - max (ν.rowLen R - m) (rowCountLt T R i) : ℕ)
        : ℤ) := Nat.cast_nonneg _
      linarith

/-- **The lattice condition on the reverse row word is the row-count condition.** -/
theorem isLatticeFrom_iff (κ : Weight d) (T : _root_.SemistandardYoungTableau ν) :
    IsLatticeFrom κ (reverseRowWord T) ↔ IsLattice κ T := by
  refine ⟨fun h r i hi => ?_, fun h => isLatticeFrom_rowsWord h _⟩
  rw [kap_of_lt κ hi, kap_of_lt κ (by omega)]
  rcases lt_or_ge r (ν.colLen 0) with hr | hr
  · -- the prefix: the rows above `r`, then the entries `≥ i + 1` of row `r`
    have hn := T.rowCountLt_le_rowLen r (i + 1)
    have hlen : (rowsWord T r).length + (ν.rowLen r - rowCountLt T r (i + 1)) ≤
        (reverseRowWord T).length := by
      have := length_rowsWord_mono T (Nat.succ_le_of_lt hr)
      simp only [rowsWord, List.length_append, length_rowWord] at this
      exact le_trans (by omega) this
    have hk := h _ hlen
    have hlen' : (rowsWord T r).length + (ν.rowLen r - rowCountLt T r (i + 1)) ≤
        (rowsWord T (r + 1)).length := by
      simp only [rowsWord, List.length_append, length_rowWord]
      omega
    have hpre : (reverseRowWord T).take ((rowsWord T r).length +
        (ν.rowLen r - rowCountLt T r (i + 1))) =
          rowsWord T r ++ (rowWord T r).take (ν.rowLen r - rowCountLt T r (i + 1)) := by
      rw [reverseRowWord, take_rowsWord T (Nat.succ_le_of_lt hr) hlen', rowsWord,
        List.take_length_add_append]
    have hstep := hk (Fin.mk_le_mk.mpr (Nat.le_succ i) : (⟨i, by omega⟩ : Fin d) ≤ ⟨i + 1, hi⟩)
    simp only [Pi.add_apply, hpre, List.count_append, count_rowsWord,
      count_take_rowWord T r _ (Nat.sub_le _ _)] at hstep
    have g1 := T.rowCountLt_mono r (Nat.le_succ i)
    have e1 : rowCountLt T r (i + 1 + 1) -
        max (ν.rowLen r - (ν.rowLen r - rowCountLt T r (i + 1))) (rowCountLt T r (i + 1)) =
          rowCount T r (i + 1) := by
      simp only [rowCount]
      omega
    have e2 : rowCountLt T r (i + 1) -
        max (ν.rowLen r - (ν.rowLen r - rowCountLt T r (i + 1))) (rowCountLt T r i) = 0 := by
      omega
    rw [e1, e2] at hstep
    rw [countBelow_succ]
    push_cast at hstep ⊢
    linarith
  · -- below the shape: the whole word
    have hk := h _ le_rfl
    have hstep := hk (Fin.mk_le_mk.mpr (Nat.le_succ i) : (⟨i, by omega⟩ : Fin d) ≤ ⟨i + 1, hi⟩)
    simp only [Pi.add_apply, List.take_length, reverseRowWord, count_rowsWord] at hstep
    rw [countBelow_of_colLen_le T _ (by omega : ν.colLen 0 ≤ r + 1),
      countBelow_of_colLen_le T _ hr]
    exact hstep

instance (κ : Weight d) : DecidablePred (fun T : _root_.SemistandardYoungTableau ν =>
    IsLatticeFrom κ (reverseRowWord T)) := fun T =>
  decidable_of_iff _ (isLatticeFrom_iff κ T).symm

/-- **The Littlewood–Richardson rule**, in reading-word form:
`a_{κ + δ} · s_ν = ∑ a_{κ + wt(T) + δ}` over the tableaux of shape `ν` in the letters
`0, …, d − 1` whose reverse row word is lattice from `κ`. -/
theorem alternant_mul_schur_word (κ : Weight d) (hκ : Antitone κ) (ν : YoungDiagram) :
    alternant (κ + staircase d) * toLaurent (TauCeti.diagramSchurPoly d ℤ ν) =
      ∑ T ∈ Finset.univ.filter
          (fun T : TauCeti.BoundedSSYT d ν => IsLatticeFrom κ (reverseRowWord T.1)),
        alternant (κ + weightVec T + staircase d) := by
  rw [alternant_mul_schur κ hκ ν]
  exact Finset.sum_congr (Finset.filter_congr fun T _ => (isLatticeFrom_iff κ T.1).symm)
    fun _ _ => rfl

end

end Schubert.RS.LR
