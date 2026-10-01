import Schubert.RS.Quiver.Schur.Projector
import TauCeti.Combinatorics.Young.BenderKnuth

/-!
# Row counts of tableaux and the lattice condition

For a semistandard tableau `T`, `rowCount T r x` is the number of entries `x` in row `r`, and
`countBelow T R x` the number of entries `x` in the rows above row `R`. Both are read off Tau Ceti's
`SemistandardYoungTableau.rowCountLt` (the number of entries smaller than a letter in a row).

The Littlewood–Richardson rule (`Schubert.RS.LR.alternant_mul_schur`) is a sum over the tableaux
whose reverse row word is *lattice from `κ`*: reading the rows top to bottom, each right to left,
`κ` plus the content read so far stays weakly decreasing. Along row `r` the balance between the
letters `i` and `i + 1` is lowest once all the `(i + 1)`s of the row are read and before its `i`s,
so the condition is one inequality per row and letter, linear in the row counts
(`Schubert.RS.LR.IsLattice`):

  `κ_{i+1} + #{i + 1 in rows ≤ r} ≤ κ_i + #{i in rows < r}`.

The equivalence with the reading-word form is `Schubert.RS.LR.isLatticeFrom_iff`
(`Schubert/RS/LR/Word.lean`).

## Main definitions

* `Schubert.RS.LR.rowCount`, `Schubert.RS.LR.countBelow`: row counts.
* `Schubert.RS.LR.kap`: an integer weight read as a function of the letter.
* `Schubert.RS.LR.IsLattice`: the lattice condition, row-count form.
* `Schubert.RS.LR.weightVec`: the content of a bounded tableau, as an integer weight.
-/

namespace Schubert.RS.LR

noncomputable section

open SemistandardYoungTableau

variable {ν : YoungDiagram}

/-! ### Row counts -/

/-- The number of entries `x` in row `r` of a tableau. -/
def rowCount (T : _root_.SemistandardYoungTableau ν) (r x : ℕ) : ℕ :=
  rowCountLt T r (x + 1) - rowCountLt T r x

/-- The number of entries `x` in the rows `0, …, R − 1` of a tableau. -/
def countBelow (T : _root_.SemistandardYoungTableau ν) (R x : ℕ) : ℕ :=
  ∑ r ∈ Finset.range R, rowCount T r x

@[simp]
theorem countBelow_zero (T : _root_.SemistandardYoungTableau ν) (x : ℕ) : countBelow T 0 x = 0 := by
  simp [countBelow]

theorem countBelow_succ (T : _root_.SemistandardYoungTableau ν) (R x : ℕ) :
    countBelow T (R + 1) x = countBelow T R x + rowCount T R x :=
  Finset.sum_range_succ _ _

theorem countBelow_mono (T : _root_.SemistandardYoungTableau ν) (x : ℕ) {R R' : ℕ}
    (h : R ≤ R') : countBelow T R x ≤ countBelow T R' x :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

theorem rowCount_eq_zero_of_colLen_le (T : _root_.SemistandardYoungTableau ν) {r : ℕ}
    (hr : ν.colLen 0 ≤ r) (x : ℕ) : rowCount T r x = 0 := by
  simp [rowCount, rowCountLt_eq_zero_of_colLen_le T hr]

/-- Below the last row, the counts no longer change. -/
theorem countBelow_of_colLen_le (T : _root_.SemistandardYoungTableau ν) (x : ℕ) {R : ℕ}
    (hR : ν.colLen 0 ≤ R) : countBelow T R x = countBelow T (ν.colLen 0) x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hR
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← add_assoc, countBelow_succ, ih (Nat.le_add_right _ _),
      rowCount_eq_zero_of_colLen_le T (Nat.le_add_right _ _), add_zero]

/-- **The content counts row by row.** -/
theorem content_eq_countBelow (T : _root_.SemistandardYoungTableau ν) (x : ℕ) :
    content T x = countBelow T (ν.colLen 0) x :=
  content_eq_sum T x

theorem content_eq_countBelow_of_le (T : _root_.SemistandardYoungTableau ν) (x : ℕ) {R : ℕ}
    (hR : ν.colLen 0 ≤ R) : content T x = countBelow T R x := by
  rw [content_eq_countBelow, countBelow_of_colLen_le T x hR]

theorem countBelow_le_content (T : _root_.SemistandardYoungTableau ν) (R x : ℕ) :
    countBelow T R x ≤ content T x := by
  rcases le_total R (ν.colLen 0) with h | h
  · rw [content_eq_countBelow]
    exact countBelow_mono T x h
  · rw [content_eq_countBelow_of_le T x h]

/-! ### The lattice condition -/

variable {d : ℕ}

/-- An integer weight, read as a function of the letter (zero beyond the alphabet). -/
def kap (κ : Weight d) (i : ℕ) : ℤ := if h : i < d then κ ⟨i, h⟩ else 0

theorem kap_of_lt (κ : Weight d) {i : ℕ} (h : i < d) : kap κ i = κ ⟨i, h⟩ := by
  simp [kap, h]

@[simp]
theorem kap_val (κ : Weight d) (i : Fin d) : kap κ i = κ i := by
  rw [kap_of_lt κ i.isLt]

/-- **The lattice condition, row-count form**: for every row `r` and every letter `i` with
`i + 1 < d`, `κ_{i+1} + #{i + 1 in rows ≤ r} ≤ κ_i + #{i in rows < r}`. This is the condition that
`κ` plus the content of every prefix of the reverse row word stays weakly decreasing
(`Schubert.RS.LR.isLatticeFrom_iff`). -/
def IsLattice (κ : Weight d) (T : _root_.SemistandardYoungTableau ν) : Prop :=
  ∀ r i : ℕ, i + 1 < d → kap κ (i + 1) + countBelow T (r + 1) (i + 1) ≤ kap κ i + countBelow T r i

/-- It suffices to check the rows up to the height of the shape. -/
theorem isLattice_iff_le (κ : Weight d) (T : _root_.SemistandardYoungTableau ν) :
    IsLattice κ T ↔ ∀ r ≤ ν.colLen 0, ∀ i < d, i + 1 < d →
      kap κ (i + 1) + countBelow T (r + 1) (i + 1) ≤ kap κ i + countBelow T r i := by
  refine ⟨fun h r _ i _ hi => h r i hi, fun h r i hi => ?_⟩
  rcases le_total r (ν.colLen 0) with hr | hr
  · exact h r hr i (by omega) hi
  · have h' := h (ν.colLen 0) le_rfl i (by omega) hi
    rwa [countBelow_of_colLen_le T _ (by omega : ν.colLen 0 ≤ r + 1),
      countBelow_of_colLen_le T _ hr, ← countBelow_of_colLen_le T _ (by omega :
        ν.colLen 0 ≤ ν.colLen 0 + 1)]

instance (κ : Weight d) : DecidablePred (IsLattice (ν := ν) κ) := fun T =>
  decidable_of_iff _ (isLattice_iff_le κ T).symm

/-- The content of a bounded tableau, as an integer weight. -/
def weightVec (T : TauCeti.BoundedSSYT d ν) : Weight d := fun i => (content T.1 i : ℤ)

/-- **A lattice tableau ends at a weakly decreasing weight.** -/
theorem antitone_add_weightVec {κ : Weight d} {T : TauCeti.BoundedSSYT d ν}
    (h : IsLattice κ T.1) : Antitone (κ + weightVec T) := by
  have hstep : ∀ i : ℕ, ∀ hi : i + 1 < d,
      (κ + weightVec T) ⟨i + 1, hi⟩ ≤ (κ + weightVec T) ⟨i, by omega⟩ := by
    intro i hi
    have h1 := h (ν.colLen 0) i hi
    rw [countBelow_of_colLen_le T.1 _ (Nat.le_succ _), ← content_eq_countBelow,
      ← content_eq_countBelow, kap_of_lt κ hi, kap_of_lt κ (by omega)] at h1
    simpa [weightVec] using h1
  intro a b hab
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  simp only [Fin.mk_le_mk] at hab
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    exact (hstep (a + m) (by omega)).trans (ih (by omega) (by omega))

end

end Schubert.RS.LR
