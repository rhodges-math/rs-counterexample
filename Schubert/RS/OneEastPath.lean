import Schubert.RS.LatticePathOrder
import Mathlib.Data.Nat.Find

/-! Identity-matching paths in the Hall determinant have one east step.
Its height determines the path on its entire active time interval. -/

namespace Schubert.RS

def oneEastHorizontal (s r t : ℕ) : ℤ := if t ≤ s+r then s else s+1

def oneEastPath (s y r : ℕ) (hr : r ≤ y) : DiagonalLatticePath s (s+1) y where
  horizontal := oneEastHorizontal s r
  nonempty := by omega
  source := by simp [oneEastHorizontal]
  target := by simp [oneEastHorizontal, show ¬s+1+y ≤ s+r by omega]
  step t hst hte := by
    simp only [oneEastHorizontal]
    split_ifs <;> omega

/-- No additional choices remain in an identity-matching path: there is a
single east-step height, between zero and the endpoint height. -/
theorem oneEastPath_classification (s y : ℕ) (P : DiagonalLatticePath s (s+1) y) :
    ∃ r ≤ y, ∀ t, s ≤ t → t ≤ s+1+y → P.horizontal t = oneEastHorizontal s r t := by
  have hex : ∃ t, s ≤ t ∧ P.horizontal t = (s+1 : ℕ) :=
    ⟨s+1+y, P.nonempty, P.target⟩
  let k := Nat.find hex
  have hk : s ≤ k ∧ P.horizontal k = (s+1 : ℕ) := Nat.find_spec hex
  have hke : k ≤ s+1+y := Nat.find_min' hex ⟨P.nonempty, P.target⟩
  have hsk : s < k := by
    by_contra hn
    have he : k = s := by omega
    rw [he, P.source] at hk
    omega
  refine ⟨k-s-1, by omega, ?_⟩
  intro t hst hte
  have he : s + (k-s-1) + 1 = k := by omega
  by_cases ht : t < k
  · have hn : ¬(s ≤ t ∧ P.horizontal t = (s+1 : ℕ)) := Nat.find_min hex ht
    have hlo := (northEast_interval_bounds P.horizontal s (s+1+y) P.step s t
      le_rfl hst hte).1
    have hhi := P.horizontal_le_target t hst hte
    rw [P.source] at hlo
    have hval : P.horizontal t = s := by omega
    simp only [oneEastHorizontal, if_pos (show t ≤ s+(k-s-1) by omega)]
    exact hval
  · have hlo := (northEast_interval_bounds P.horizontal s (s+1+y) P.step k t
      hk.1 (by omega) hte).1
    have hhi := P.horizontal_le_target t hst hte
    rw [hk.2] at hlo
    have hval : P.horizontal t = (s+1 : ℕ) := by omega
    simp only [oneEastHorizontal, if_neg (show ¬t ≤ s+(k-s-1) by omega)]
    simpa only [Int.natCast_add, Int.natCast_one] using hval

/-- Adjacent one-east paths meet on their common vertical line exactly
when the left path's east step is no higher than the right path's step. -/
theorem adjacent_oneEast_intersection (s y z r q : ℕ)
    (hr : r ≤ y) (hq : q ≤ z) (hyz : y ≤ z) :
    (∃ t, s+1 ≤ t ∧ t ≤ s+2+y ∧ t ≤ s+1+z ∧
      oneEastHorizontal (s+1) r t = oneEastHorizontal s q t) ↔ q ≤ r := by
  constructor
  · rintro ⟨t, ht, hty, htz, he⟩
    unfold oneEastHorizontal at he
    split_ifs at he <;> omega
  · intro hqr
    refine ⟨s+q+1, by omega, by omega, by omega, ?_⟩
    simp only [oneEastHorizontal,
      if_pos (show s+q+1 ≤ s+1+r by omega),
      if_neg (show ¬s+q+1 ≤ s+q by omega)]
    simp

end Schubert.RS
