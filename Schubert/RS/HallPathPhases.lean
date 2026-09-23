import Schubert.RS.HallLattice

/-! Private padding and the exact active interval of each Hall lattice path. -/

namespace Schubert.RS.HallLattice
noncomputable section
variable {d M : ℕ} (y : Fin d → Fin (M+1))

theorem edge_into_start (t : Fin (d+M+2)) (v : Vertex d M) (j : Fin d)
    (h : edges y t v (start j)) : v = start j := by
  rcases v with k | p | i <;> simp only [edges, start] at h ⊢
  exact congrArg Sum.inl h.1

theorem edge_out_of_finish (t : Fin (d+M+2)) (v : Vertex d M) (i : Fin d)
    (h : edges y t (finish i) v) : v = finish i := by
  rcases v with k | p | j <;> simp only [edges, finish] at h ⊢
  rw [h]

variable {j i : Fin d} (P : LayeredPath (edges y) (start j) (finish i))

theorem path_start_label (t : Fin (d+M+3)) (k : Fin d) (hk : P.vertex t = start k) : k = j := by
  induction t using Fin.induction with
  | zero =>
    rw [P.start] at hk
    exact (Sum.inl.inj hk).symm
  | succ t ih =>
    apply ih
    apply edge_into_start y t _ k
    rw [← hk]
    exact P.edges t

theorem path_finish_label (t : Fin (d+M+3)) (k : Fin d) (hk : P.vertex t = finish k) : k = i := by
  induction t using Fin.reverseInduction with
  | last =>
    rw [P.finish] at hk
    exact (finish_injective hk).symm
  | cast t ih =>
    apply ih
    apply edge_out_of_finish y t _ k
    rw [← hk]
    exact P.edges t

theorem path_active_grid (t : Fin (d+M+3))
    (hs : hallSource j < t.val) (he : t.val ≤ endpointTime y i) :
    ∃ p : Fin (d+1) × Fin (M+1), P.vertex t = .inr (.inl p) := by
  have ht := path_vertex_time y j i P t
  rcases hv : P.vertex t with k | p | k
  · have hk := path_start_label y P t k hv
    subst k
    rw [hv] at ht
    change t.val ≤ hallSource j at ht
    omega
  · exact ⟨p, rfl⟩
  · have hk := path_finish_label y P t k hv
    subst k
    rw [hv] at ht
    change endpointTime y i+1 ≤ t.val at ht
    omega

theorem path_before_start (t : Fin (d+M+3)) (ht : t.val ≤ hallSource j) :
    P.vertex t = start j := by
  induction t using Fin.induction with
  | zero => exact P.start
  | succ t ih =>
    have hp := ih (by change t.val ≤ hallSource j; change t.val+1 ≤ hallSource j at ht; omega)
    have he := P.edges t
    rw [hp] at he
    rcases hq : P.vertex t.succ with k | q | l <;> rw [hq] at he <;>
      simp only [edges, start] at he
    · exact congrArg Sum.inl he.1.symm
    · change t.val+1 ≤ hallSource j at ht
      omega

theorem path_after_finish (t : Fin (d+M+3)) (ht : endpointTime y i < t.val) :
    P.vertex t = finish i := by
  induction t using Fin.reverseInduction with
  | last => exact P.finish
  | cast t ih =>
    have hn := ih (by change endpointTime y i < t.val+1; change endpointTime y i < t.val at ht; omega)
    have he := P.edges t
    rw [hn] at he
    rcases hp : P.vertex t.castSucc with k | p | l <;> rw [hp] at he <;>
      simp only [edges, finish] at he
    · change endpointTime y i < t.val at ht
      omega
    · exact congrArg (fun k => Sum.inr (Sum.inr k)) he

end
end Schubert.RS.HallLattice
