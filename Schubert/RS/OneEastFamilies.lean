import Schubert.RS.OneEastPath
import Mathlib.Order.Fin.Basic

/-! The complete nonintersection criterion for the Hall determinant survivors. -/

namespace Schubert.RS

def hallSource {d : ℕ} (i : Fin d) : ℕ := d-1-i.val

def OneEastFamilyDisjoint {d : ℕ} (y r : Fin d → ℕ) : Prop :=
  ∀ i j, i < j → ¬∃ t, hallSource i ≤ t ∧ hallSource j ≤ t ∧
    t ≤ hallSource i+1+y i ∧ t ≤ hallSource j+1+y j ∧
      oneEastHorizontal (hallSource i) (r i) t = oneEastHorizontal (hallSource j) (r j) t

theorem strictMono_oneEastFamilyDisjoint {d : ℕ} (y r : Fin d → ℕ) (hr : StrictMono r) :
    OneEastFamilyDisjoint y r := by
  intro i j hij
  rintro ⟨t, hit, hjt, hte, hte', he⟩
  have hi := i.isLt
  have hj := j.isLt
  have hijv : i.val < j.val := hij
  have hrij := hr hij
  unfold hallSource oneEastHorizontal at he
  split_ifs at he <;> omega

/-- Adjacent intersections are the only obstructions: nonadjacent paths
cannot share a horizontal coordinate. The converse covers every pair. -/
theorem oneEastFamilyDisjoint_iff_strictMono {d : ℕ} (y r : Fin d → ℕ)
    (hy : Monotone y) (hr : ∀ i, r i ≤ y i) :
    OneEastFamilyDisjoint y r ↔ StrictMono r := by
  constructor
  · intro hd
    cases d with
    | zero => intro i; exact Fin.elim0 i
    | succ d =>
      apply Fin.strictMono_iff_lt_succ.mpr
      intro i
      have hij : i.castSucc < i.succ := Fin.castSucc_lt_succ
      have hs : hallSource i.castSucc = hallSource i.succ + 1 := by
        have hi := i.isLt
        simp only [hallSource, Fin.val_castSucc, Fin.val_succ]
        omega
      by_contra hn
      have hh : r i.succ ≤ r i.castSucc := by omega
      obtain ⟨t, ht, hte, hte', he⟩ :=
        (adjacent_oneEast_intersection (hallSource i.succ)
          (y i.castSucc) (y i.succ) (r i.castSucc) (r i.succ)
          (hr _) (hr _) (hy hij.le)).mpr hh
      apply hd i.castSucc i.succ hij
      refine ⟨t, ?_, by omega, ?_, hte', ?_⟩
      · rw [hs]; exact ht
      · rw [hs]; omega
      · rw [hs]; exact he
  · exact strictMono_oneEastFamilyDisjoint y r

end Schubert.RS
