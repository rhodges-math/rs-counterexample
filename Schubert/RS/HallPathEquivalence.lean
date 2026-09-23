import Schubert.RS.HallPathEncode

/-! Padding loses no path: inverse and active-interval extensionality. -/

namespace Schubert.RS.HallLattice
noncomputable section
variable {d M : ℕ} (y : Fin d → Fin (M+1)) {j i : Fin d}

theorem latticePoint_decoded
    (P : LayeredPath (edges y) (start j) (finish i))
    (t : ℕ) (hs : hallSource j ≤ t) (he : t ≤ hallSource i+1+(y i).val)
    (ht : t+1 < d+M+3) (p : Fin (d+1) × Fin (M+1))
    (hp : P.vertex ⟨t+1, ht⟩ = .inr (.inl p)) :
    latticePoint y (decodedPath y P) t hs he = p := by
  have hx := latticePoint_horizontal y (decodedPath y P) t hs he
  have hz := latticePoint_vertical y (decodedPath y P) t hs he
  change _ = pathHorizontal y P t at hx
  change _ = (t : ℤ)-pathHorizontal y P t at hz
  rw [pathHorizontal_grid y P t ht p hp] at hx hz
  have htime := path_vertex_time y j i P ⟨t+1, ht⟩
  rw [hp] at htime
  change t+1 = p.1.val+p.2.val+1 at htime
  apply Prod.ext <;> apply Fin.ext
  · exact_mod_cast hx
  · omega

theorem encoded_decoded (P : LayeredPath (edges y) (start j) (finish i)) :
    encodedPath y (decodedPath y P) = P := by
  apply LayeredPath.ext
  funext t
  change paddedVertex y (decodedPath y P) t = P.vertex t
  by_cases hs : t.val ≤ hallSource j
  · rw [paddedVertex_before y _ t hs, path_before_start y P t hs]
  · by_cases he : endpointTime y i < t.val
    · rw [paddedVertex_after y _ t he, path_after_finish y P t he]
    · have hstart : hallSource j < t.val := by omega
      have hend : t.val ≤ endpointTime y i := by omega
      obtain ⟨p, hp⟩ := path_active_grid y P t hstart hend
      rw [paddedVertex_active y _ t hstart hend, hp]
      have hlocal : t.val-1+1 = t.val := by omega
      have ht : t.val-1+1 < d+M+3 := by rw [hlocal]; exact t.isLt
      have hp' : P.vertex ⟨t.val-1+1, ht⟩ = .inr (.inl p) := by
        convert hp using 1
        apply congrArg P.vertex
        exact Fin.ext hlocal
      rw [latticePoint_decoded y P _ _ _ ht p hp']

theorem decoded_encoded_horizontal
    (P : DiagonalLatticePath (hallSource j) (hallSource i+1) (y i).val)
    (t : ℕ) (hs : hallSource j ≤ t) (he : t ≤ hallSource i+1+(y i).val) :
    pathHorizontal y (encodedPath y P) t = P.horizontal t := by
  have ht := active_tick_bound y t he
  have hstart : hallSource j < (⟨t+1, ht⟩ : Fin (d+M+3)).val := by simp; omega
  have hend : (⟨t+1, ht⟩ : Fin (d+M+3)).val ≤ endpointTime y i := by
    change t+1 ≤ endpointTime y i
    unfold endpointTime
    omega
  have hp : (encodedPath y P).vertex ⟨t+1, ht⟩ = .inr (.inl (latticePoint y P t hs he)) := by
    change paddedVertex y P _ = _
    simpa only [Nat.add_sub_cancel] using paddedVertex_active y P ⟨t+1, ht⟩ hstart hend
  rw [pathHorizontal_grid y (encodedPath y P) t ht _ hp]
  exact latticePoint_horizontal y P t hs he

theorem path_ext_active (P Q : LayeredPath (edges y) (start j) (finish i))
    (h : ∀ t, hallSource j ≤ t → t ≤ hallSource i+1+(y i).val →
      pathHorizontal y P t = pathHorizontal y Q t) : P = Q := by
  rw [← encoded_decoded y P, ← encoded_decoded y Q]
  apply LayeredPath.ext
  funext t
  change paddedVertex y (decodedPath y P) t = paddedVertex y (decodedPath y Q) t
  by_cases hs : t.val ≤ hallSource j
  · rw [paddedVertex_before y _ t hs, paddedVertex_before y _ t hs]
  · by_cases he : endpointTime y i < t.val
    · rw [paddedVertex_after y _ t he, paddedVertex_after y _ t he]
    · have hstart : hallSource j < t.val := by omega
      have hend : t.val ≤ endpointTime y i := by omega
      rw [paddedVertex_active y _ t hstart hend, paddedVertex_active y _ t hstart hend]
      apply congrArg (fun p => Sum.inr (Sum.inl p))
      apply Prod.ext <;> apply Fin.ext
      · have hp := latticePoint_horizontal y (decodedPath y P) (t.val-1) (by omega) (by
          unfold endpointTime at hend; omega)
        have hq := latticePoint_horizontal y (decodedPath y Q) (t.val-1) (by omega) (by
          unfold endpointTime at hend; omega)
        change _ = pathHorizontal y P _ at hp
        change _ = pathHorizontal y Q _ at hq
        rw [h _ (by omega) (by unfold endpointTime at hend; omega)] at hp
        omega
      · have hp := latticePoint_vertical y (decodedPath y P) (t.val-1) (by omega) (by
          unfold endpointTime at hend; omega)
        have hq := latticePoint_vertical y (decodedPath y Q) (t.val-1) (by omega) (by
          unfold endpointTime at hend; omega)
        change _ = (↑(t.val-1) : ℤ)-pathHorizontal y P _ at hp
        change _ = (↑(t.val-1) : ℤ)-pathHorizontal y Q _ at hq
        rw [h _ (by omega) (by unfold endpointTime at hend; omega)] at hp
        omega

end
end Schubert.RS.HallLattice
