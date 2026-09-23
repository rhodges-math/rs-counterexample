import Schubert.RS.HallPathEquivalence

/-! Read actual finite-grid edge coordinates without changing the path model. -/

namespace Schubert.RS.HallLattice
noncomputable section
variable {d M : ℕ} (y : Fin d → Fin (M+1)) {j i : Fin d}
variable (P : LayeredPath (edges y) (start j) (finish i))

theorem active_edge_coordinates (t : Fin (d+M+2))
    (hs : hallSource j < t.val) (he : t.val < endpointTime y i) :
    ∃ p q : Fin (d+1) × Fin (M+1),
      P.vertex t.castSucc = .inr (.inl p) ∧ P.vertex t.succ = .inr (.inl q) ∧
      pathHorizontal y P (t.val-1) = p.1.val ∧ pathHorizontal y P t.val = q.1.val ∧
      t.val = p.1.val+p.2.val+1 := by
  obtain ⟨p, hp⟩ := path_active_grid y P t.castSucc hs (by change t.val ≤ endpointTime y i; omega)
  obtain ⟨q, hq⟩ := path_active_grid y P t.succ (by change hallSource j < t.val+1; omega)
    (by change t.val+1 ≤ endpointTime y i; omega)
  have hpos : 1 ≤ t.val := by omega
  have hlocal : t.val-1+1 = t.val := Nat.sub_add_cancel hpos
  have ht : t.val-1+1 < d+M+3 := by rw [hlocal]; have h := t.isLt; omega
  have hp' : P.vertex ⟨t.val-1+1, ht⟩ = .inr (.inl p) := by
    convert hp using 1
    apply congrArg P.vertex
    exact Fin.ext hlocal
  have htime := path_vertex_time y j i P t.castSucc
  rw [hp] at htime
  exact ⟨p, q, hp, hq, pathHorizontal_grid y P _ ht p hp',
    pathHorizontal_grid y P t.val (by have h := t.isLt; omega) q hq, htime⟩

theorem inactive_edgeWeight {R : Type*} [CommRing R] (slot : Fin (M+1) → R)
    (t : Fin (d+M+2)) (h : t.val ≤ hallSource j ∨ endpointTime y i ≤ t.val) :
    edgeWeight slot t (P.vertex t.castSucc) (P.vertex t.succ) = 1 := by
  rcases h with hs | he
  · rw [path_before_start y P t.castSucc hs]
    rfl
  · rw [path_after_finish y P t.succ (by change endpointTime y i < t.val+1; omega)]
    cases P.vertex t.castSucc with
    | inl j => rfl
    | inr p => cases p <;> rfl

end
end Schubert.RS.HallLattice
