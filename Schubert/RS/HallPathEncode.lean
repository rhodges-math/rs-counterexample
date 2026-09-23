import Schubert.RS.HallLatticePoints

/-! Add the private source/sink padding to a genuine north/east lattice path. -/

namespace Schubert.RS.HallLattice
noncomputable section
variable {d M : ℕ} (y : Fin d → Fin (M+1)) {j i : Fin d}
variable (P : DiagonalLatticePath (hallSource j) (hallSource i+1) (y i).val)

def paddedVertex (t : Fin (d+M+3)) : Vertex d M :=
  if hs : t.val ≤ hallSource j then start j
  else if he : endpointTime y i < t.val then finish i
  else .inr (.inl (latticePoint y P (t.val-1) (by omega) (by
    unfold endpointTime at he
    omega)))

theorem paddedVertex_before (t : Fin (d+M+3)) (ht : t.val ≤ hallSource j) :
    paddedVertex y P t = start j := by
  simp only [paddedVertex, dif_pos ht]

theorem paddedVertex_after (t : Fin (d+M+3)) (ht : endpointTime y i < t.val) :
    paddedVertex y P t = finish i := by
  have hn : ¬t.val ≤ hallSource j := by
    have h := P.nonempty
    unfold endpointTime at ht
    omega
  simp only [paddedVertex, dif_neg hn, dif_pos ht]

theorem paddedVertex_active (t : Fin (d+M+3))
    (hs : hallSource j < t.val) (he : t.val ≤ endpointTime y i) :
    paddedVertex y P t = .inr (.inl (latticePoint y P (t.val-1) (by omega) (by
      unfold endpointTime at he
      omega))) := by
  simp only [paddedVertex, dif_neg (not_le.mpr hs), dif_neg (not_lt.mpr he)]

theorem paddedVertex_edges (t : Fin (d+M+2)) :
    edges y t (paddedVertex y P t.castSucc) (paddedVertex y P t.succ) := by
  have hn := P.nonempty
  by_cases ht : t.val < hallSource j
  · rw [paddedVertex_before y P t.castSucc (by change t.val ≤ hallSource j; omega),
      paddedVertex_before y P t.succ (by change t.val+1 ≤ hallSource j; omega)]
    exact ⟨rfl, ht⟩
  · by_cases heq : t.val = hallSource j
    · rw [paddedVertex_before y P t.castSucc (by change t.val ≤ hallSource j; omega)]
      have hs : hallSource j < t.succ.val := by change hallSource j < t.val+1; omega
      have he : t.succ.val ≤ endpointTime y i := by
        change t.val+1 ≤ endpointTime y i
        unfold endpointTime
        omega
      rw [paddedVertex_active y P t.succ hs he]
      have hlocal : t.succ.val-1 = hallSource j := by simp [heq]
      simp only [hlocal, latticePoint_source]
      exact ⟨heq, rfl, rfl⟩
    · have hs : hallSource j < t.val := by omega
      by_cases hend : endpointTime y i < t.val
      · rw [paddedVertex_after y P t.castSucc (by exact hend),
          paddedVertex_after y P t.succ (by change endpointTime y i < t.val+1; omega)]
        exact rfl
      · have hle : t.val ≤ endpointTime y i := by omega
        by_cases heqend : t.val = endpointTime y i
        · rw [paddedVertex_active y P t.castSucc hs hle,
            paddedVertex_after y P t.succ (by change endpointTime y i < t.val+1; omega)]
          have hlocal : t.castSucc.val-1 = hallSource i+1+(y i).val := by
            change t.val-1 = hallSource i+1+(y i).val
            unfold endpointTime at heqend
            omega
          simp only [hlocal, latticePoint_endpoint]
          exact ⟨heqend, rfl, rfl⟩
        · have hlt : t.val < endpointTime y i := by omega
          rw [paddedVertex_active y P t.castSucc hs hle,
            paddedVertex_active y P t.succ (by change hallSource j < t.val+1; omega)
              (by change t.val+1 ≤ endpointTime y i; omega)]
          have hstart : hallSource j ≤ t.val-1 := by omega
          have hstop : t.val-1 < hallSource i+1+(y i).val := by
            unfold endpointTime at hlt
            omega
          have hstep := latticePoint_step y P (t.val-1) hstart hstop
          have htpos : 1 ≤ t.val := by omega
          simpa only [edges, Fin.val_castSucc, Fin.val_succ, Nat.add_sub_cancel,
            Nat.sub_add_cancel htpos] using hstep

def encodedPath : LayeredPath (edges y) (start j) (finish i) where
  vertex := paddedVertex y P
  start := paddedVertex_before y P 0 (Nat.zero_le _)
  finish := paddedVertex_after y P (Fin.last (d+M+2)) (by
    have h := endpoint_bound y i
    change endpointTime y i < d+M+2
    omega)
  edges := paddedVertex_edges y P

end
end Schubert.RS.HallLattice
