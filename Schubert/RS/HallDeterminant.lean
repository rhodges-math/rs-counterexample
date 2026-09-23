import Schubert.RS.HallRowWeight
import Schubert.RS.HallSurvivorEquivalence

/-! The Hall determinant identity, proved by complete path enumeration and
the paper's first-tail involution. Heights are zero based and every row
alphabet is nonempty, as in the concrete counterexample. -/

namespace Schubert.RS
noncomputable section

def completeHomogeneous {R : Type*} [CommRing R] {M : ℕ}
    (slot : Fin (M+1) → R) (y : Fin (M+1)) (z : ℤ) : R :=
  if 0 ≤ z then ∑ r : HallLattice.WeakHeights z.toNat y.val, ∏ q,
    slot ⟨(r.val q).val, by have h := y.isLt; have hr := (r.val q).isLt; omega⟩ else 0

namespace HallLattice
variable {d M : ℕ} (y : Fin d → Fin (M+1))
variable {R : Type*} [CommRing R] (slot : Fin (M+1) → R)

theorem row_path_sum_eq_completeHomogeneous (i j : Fin d) :
    (∑ P : LayeredPath (edges y) (start j) (finish i), layeredPathWeight (edgeWeight slot) P) =
      completeHomogeneous slot (y i) (1-(i.val : ℤ)+j.val) := by
  classical
  by_cases hz : 0 ≤ 1-(i.val : ℤ)+j.val
  · have hk : hallSource j+(1-(i.val : ℤ)+j.val).toNat = hallSource i+1 := by
      have hnat := Int.toNat_of_nonneg hz
      have hi := i.isLt
      have hj := j.isLt
      unfold hallSource
      omega
    rw [completeHomogeneous, if_pos hz]
    exact row_path_sum y hk slot
  · have hn : hallSource i+1 < hallSource j := by
      have hi := i.isLt
      have hj := j.isLt
      unfold hallSource
      omega
    letI := no_path_negative_degree y hn
    simp only [completeHomogeneous, if_neg hz, Finset.univ_eq_empty, Finset.sum_empty]

/-- Complete homogeneous rows yield precisely the strictly increasing
bounded columns. All repeated-slot terms have been cancelled, not removed. -/
theorem hall_determinant (hy : Monotone (fun i => (y i).val)) :
    Matrix.det (fun i j : Fin d => completeHomogeneous slot (y i) (1-(i.val : ℤ)+j.val)) =
      ∑ r : StrictHeights y, ∏ i, slot ⟨(r.val i).val, by
        have h := (y i).isLt; have hr := (r.val i).isLt; omega⟩ := by
  have hm : (fun i j : Fin d => completeHomogeneous slot (y i) (1-(i.val : ℤ)+j.val)) =
      (fun i j : Fin d => ∑ P : LayeredPath (edges y) (start j) (finish i),
        layeredPathWeight (edgeWeight slot) P) := by
    funext i j
    exact (row_path_sum_eq_completeHomogeneous y slot i j).symm
  rw [hm]
  exact path_determinant_strict_heights y hy slot

end HallLattice
end
end Schubert.RS
