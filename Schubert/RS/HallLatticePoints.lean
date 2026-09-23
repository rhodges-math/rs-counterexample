import Schubert.RS.HallPathMatching

/-! Realize diagonal lattice paths as points of the finite Hall grid. -/

namespace Schubert.RS.HallLattice
noncomputable section
variable {d M : ℕ} (y : Fin d → Fin (M+1)) {j i : Fin d}
variable (P : DiagonalLatticePath (hallSource j) (hallSource i+1) (y i).val)

theorem horizontal_nonnegative (t : ℕ) (hs : hallSource j ≤ t)
    (he : t ≤ hallSource i+1+(y i).val) : 0 ≤ P.horizontal t := by
  have h := (northEast_interval_bounds P.horizontal _ _ P.step _ t le_rfl hs he).1
  rw [P.source] at h
  omega

def latticePoint (t : ℕ) (hs : hallSource j ≤ t) (he : t ≤ hallSource i+1+(y i).val) :
    Fin (d+1) × Fin (M+1) :=
  (⟨(P.horizontal t).toNat, by
      have h0 := horizontal_nonnegative y P t hs he
      have hx := P.horizontal_le_target t hs he
      have hi := source_bound i
      have hn := Int.toNat_of_nonneg h0
      omega⟩,
    ⟨((t : ℤ)-P.horizontal t).toNat, by
      have ht := P.horizontal_le_time t hs he
      have hy := P.time_sub_height_le t hs he
      have hm := (y i).isLt
      have hn := Int.toNat_of_nonneg (show 0 ≤ (t : ℤ)-P.horizontal t by omega)
      omega⟩)

theorem latticePoint_horizontal (t : ℕ) (hs : hallSource j ≤ t)
    (he : t ≤ hallSource i+1+(y i).val) :
    ((latticePoint y P t hs he).1.val : ℤ) = P.horizontal t :=
  Int.toNat_of_nonneg (horizontal_nonnegative y P t hs he)

theorem latticePoint_vertical (t : ℕ) (hs : hallSource j ≤ t)
    (he : t ≤ hallSource i+1+(y i).val) :
    ((latticePoint y P t hs he).2.val : ℤ) = (t : ℤ)-P.horizontal t :=
  Int.toNat_of_nonneg (sub_nonneg.mpr (P.horizontal_le_time t hs he))

theorem latticePoint_source : latticePoint y P (hallSource j) le_rfl P.nonempty = sourcePoint j := by
  apply Prod.ext <;> apply Fin.ext
  · have h := latticePoint_horizontal y P _ le_rfl P.nonempty
    rw [P.source] at h
    exact_mod_cast h
  · have h := latticePoint_vertical y P _ le_rfl P.nonempty
    rw [P.source, sub_self] at h
    change (latticePoint y P (hallSource j) le_rfl P.nonempty).2.val = 0
    exact_mod_cast h

theorem latticePoint_endpoint :
    latticePoint y P (hallSource i+1+(y i).val) P.nonempty le_rfl = endpoint y i := by
  apply Prod.ext <;> apply Fin.ext
  · have h := latticePoint_horizontal y P _ P.nonempty le_rfl
    rw [P.target] at h
    exact_mod_cast h
  · have h := latticePoint_vertical y P _ P.nonempty le_rfl
    rw [P.target] at h
    simp only [Int.natCast_add, Int.natCast_one] at h
    have he : ((latticePoint y P (hallSource i+1+(y i).val) P.nonempty le_rfl).2.val : ℤ) = (y i).val := by omega
    exact_mod_cast he

theorem latticePoint_step (t : ℕ) (hs : hallSource j ≤ t)
    (he : t < hallSource i+1+(y i).val) :
    let p := latticePoint y P t hs he.le
    let q := latticePoint y P (t+1) (by omega) (by omega)
    (q.1.val = p.1.val+1 ∧ q.2 = p.2) ∨ (q.1 = p.1 ∧ q.2.val = p.2.val+1) := by
  dsimp only
  have hp := latticePoint_horizontal y P t hs he.le
  have hp' := latticePoint_vertical y P t hs he.le
  have hq := latticePoint_horizontal y P (t+1) (by omega) (by omega)
  have hq' := latticePoint_vertical y P (t+1) (by omega) (by omega)
  have hstep := P.step t hs he
  by_cases hx : P.horizontal (t+1) = P.horizontal t
  · right
    constructor
    · apply Fin.ext; omega
    · omega
  · left
    constructor
    · omega
    · apply Fin.ext; omega

end
end Schubert.RS.HallLattice
