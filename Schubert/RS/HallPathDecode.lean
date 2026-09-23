import Schubert.RS.HallPathEndpoints

/-! Every padded path decodes to the genuine diagonal lattice path. -/

namespace Schubert.RS.HallLattice
noncomputable section
variable {d M : ℕ} (y : Fin d → Fin (M+1))
variable {j i : Fin d} (P : LayeredPath (edges y) (start j) (finish i))

def pathHorizontal (t : ℕ) : ℤ :=
  if ht : t+1 < d+M+3 then
    match P.vertex ⟨t+1, ht⟩ with
    | .inr (.inl p) => (p.1.val : ℤ)
    | _ => 0
  else 0

theorem pathHorizontal_grid (t : ℕ) (ht : t+1 < d+M+3)
    (p : Fin (d+1) × Fin (M+1)) (hp : P.vertex ⟨t+1, ht⟩ = .inr (.inl p)) :
    pathHorizontal y P t = p.1.val := by
  simp only [pathHorizontal, dif_pos ht]
  rw [hp]

theorem active_tick_bound (t : ℕ) (ht : t ≤ hallSource i+1+(y i).val) :
    t+1 < d+M+3 := by
  have hi := endpoint_bound y i
  unfold endpointTime at hi
  omega

theorem pathHorizontal_source : pathHorizontal y P (hallSource j) = hallSource j := by
  have ht : hallSource j+1 < d+M+3 := by have hj := source_bound j; omega
  have hs : P.vertex ⟨hallSource j+1, ht⟩ = .inr (.inl (sourcePoint j)) :=
    path_source_point y P
  rw [pathHorizontal_grid y P _ ht _ hs]
  rfl

theorem pathHorizontal_target :
    pathHorizontal y P (hallSource i+1+(y i).val) = hallSource i+1 := by
  have ht := active_tick_bound y (i := i) (hallSource i+1+(y i).val) le_rfl
  have he : (⟨hallSource i+1+(y i).val+1, ht⟩ : Fin (d+M+3)) = (endpointTick y i).castSucc := by
    apply Fin.ext
    simp only [endpointTick, endpointTime, Fin.val_castSucc]
    omega
  have hp : P.vertex ⟨hallSource i+1+(y i).val+1, ht⟩ = .inr (.inl (endpoint y i)) := by
    rw [he]
    exact path_endpoint y P
  rw [pathHorizontal_grid y P _ ht _ hp]
  simp [endpoint]

theorem pathHorizontal_step (t : ℕ) (hs : hallSource j ≤ t)
    (he : t < hallSource i+1+(y i).val) :
    pathHorizontal y P t ≤ pathHorizontal y P (t+1) ∧
      pathHorizontal y P (t+1) ≤ pathHorizontal y P t+1 := by
  have ht := active_tick_bound y (i := i) t he.le
  have ht' := active_tick_bound y (i := i) (t+1) (by omega)
  obtain ⟨p, hp⟩ := path_active_grid y P ⟨t+1, ht⟩ (by simp; omega) (by
    change t+1 ≤ endpointTime y i
    unfold endpointTime
    omega)
  obtain ⟨q, hq⟩ := path_active_grid y P ⟨t+1+1, ht'⟩ (by simp; omega) (by
    change t+1+1 ≤ endpointTime y i
    unfold endpointTime
    omega)
  rw [pathHorizontal_grid y P t ht p hp, pathHorizontal_grid y P (t+1) ht' q hq]
  have hk : t+1 < d+M+2 := by omega
  have hedge := P.edges ⟨t+1, hk⟩
  change edges y ⟨t+1, hk⟩ (P.vertex ⟨t+1, ht⟩) (P.vertex ⟨t+1+1, ht'⟩) at hedge
  rw [hp, hq] at hedge
  change (q.1.val = p.1.val+1 ∧ q.2 = p.2) ∨
    (q.1 = p.1 ∧ q.2.val = p.2.val+1) at hedge
  rcases hedge with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · omega
  · rw [hx]
    omega

def decodedPath : DiagonalLatticePath (hallSource j) (hallSource i+1) (y i).val where
  horizontal := pathHorizontal y P
  nonempty := path_active_nonempty y P
  source := pathHorizontal_source y P
  target := by simpa using pathHorizontal_target y P
  step := pathHorizontal_step y P

end
end Schubert.RS.HallLattice
