import Schubert.RS.ThresholdPaths
import Mathlib.Data.Nat.Find

/-! Recover every east step of an arbitrary path, in its actual order. -/

namespace Schubert.RS
noncomputable section
variable {s k y : ℕ} (P : DiagonalLatticePath s (s+k) y)

theorem crossing_exists (q : Fin k) : ∃ t, s ≤ t ∧ (s+q.val+1 : ℕ) ≤ P.horizontal t := by
  refine ⟨s+k+y, P.nonempty, ?_⟩
  rw [P.target]
  have hq := q.isLt
  omega

def crossingTime (q : Fin k) : ℕ := Nat.find (crossing_exists P q)

theorem crossingTime_spec (q : Fin k) :
    s ≤ crossingTime P q ∧ (s+q.val+1 : ℕ) ≤ P.horizontal (crossingTime P q) :=
  Nat.find_spec (crossing_exists P q)

theorem crossingTime_le_end (q : Fin k) : crossingTime P q ≤ s+k+y := by
  apply Nat.find_min'
  refine ⟨P.nonempty, ?_⟩
  rw [P.target]
  have hq := q.isLt
  omega

theorem crossingTime_gt_source (q : Fin k) : s < crossingTime P q := by
  have h := crossingTime_spec P q
  by_contra hn
  have he : crossingTime P q = s := by omega
  rw [he, P.source] at h
  omega

theorem crossingTime_horizontal (q : Fin k) :
    P.horizontal (crossingTime P q) = (s+q.val+1 : ℕ) := by
  have hs := crossingTime_gt_source P q
  have he := crossingTime_le_end P q
  have hmin := Nat.find_min (crossing_exists P q) (show crossingTime P q-1 < crossingTime P q by omega)
  have hstep := P.step (crossingTime P q-1) (by omega) (by omega)
  have hpos : crossingTime P q-1+1 = crossingTime P q := by omega
  rw [hpos] at hstep
  have hlo := (crossingTime_spec P q).2
  omega

theorem crossingTime_le_iff (q : Fin k) (t : ℕ) (hs : s ≤ t) (he : t ≤ s+k+y) :
    crossingTime P q ≤ t ↔ (s+q.val+1 : ℕ) ≤ P.horizontal t := by
  constructor
  · intro ht
    have hmono := (northEast_interval_bounds P.horizontal s (s+k+y) P.step
      (crossingTime P q) t (crossingTime_spec P q).1 ht he).1
    rw [crossingTime_horizontal] at hmono
    exact hmono
  · intro ht
    exact Nat.find_min' (crossing_exists P q) ⟨hs, ht⟩

theorem crossingTime_strictMono : StrictMono (crossingTime P) := by
  intro q p hqp
  have hqv : q.val < p.val := hqp
  by_contra hn
  have hh := (crossingTime_le_iff P p (crossingTime P q)
    (crossingTime_spec P q).1 (crossingTime_le_end P q)).mp (by omega)
  rw [crossingTime_horizontal] at hh
  omega

def crossingHeight (q : Fin k) : Fin (y+1) :=
  ⟨crossingTime P q-s-q.val-1, by
    have hs := (crossingTime_spec P q).1
    have he := crossingTime_le_end P q
    have hx := crossingTime_horizontal P q
    have hb := P.time_sub_height_le (crossingTime P q) hs he
    have hl := P.horizontal_le_time (crossingTime P q) hs he
    omega⟩

theorem eastTime_crossingHeight (q : Fin k) :
    eastTime s (crossingHeight P) q = crossingTime P q := by
  have hs := (crossingTime_spec P q).1
  have he := crossingTime_le_end P q
  have hl := P.horizontal_le_time (crossingTime P q) hs he
  rw [crossingTime_horizontal] at hl
  simp only [eastTime, crossingHeight]
  omega

theorem crossingHeight_monotone : Monotone (fun q => (crossingHeight P q).val) := by
  cases k with
  | zero => intro i; exact Fin.elim0 i
  | succ k =>
    apply Fin.monotone_iff_le_succ.mpr
    intro q
    have hq : q.castSucc < q.succ := Fin.castSucc_lt_succ
    have hc := crossingTime_strictMono P hq
    have hi := eastTime_crossingHeight P q.castSucc
    have hj := eastTime_crossingHeight P q.succ
    simp only [eastTime, Fin.val_castSucc, Fin.val_succ] at hi hj
    omega

end
end Schubert.RS
