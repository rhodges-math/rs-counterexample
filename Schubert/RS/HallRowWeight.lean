import Schubert.RS.HallRowEquivalence
import Schubert.RS.HallEdgeCoordinates
import Schubert.RS.ThresholdEvents

/-! Complete row-path weights are the monomials of weak height words. -/

namespace Schubert.RS.HallLattice
noncomputable section
variable {d M : ℕ} (y : Fin d → Fin (M+1)) {j i : Fin d}
variable {k : ℕ} (hk : hallSource j+k = hallSource i+1)
variable (r : WeakHeights k (y i).val)
variable {R : Type*} [CommRing R] (slot : Fin (M+1) → R)

def eastTick (q : Fin k) : Fin (d+M+2) :=
  ⟨eastTime (hallSource j) r.val q, by
    have hq := q.isLt
    have hr := (r.val q).isLt
    have hs := source_bound i
    have hy := (y i).isLt
    unfold eastTime
    omega⟩

theorem eastTick_injective : Function.Injective (eastTick y hk r) := by
  intro q p h
  apply (eastTime_strictMono (hallSource j) r.val r.property).injective
  exact congrArg Fin.val h

theorem heightWord_eastWeight (q : Fin k) :
    edgeWeight slot (eastTick y hk r q)
      ((heightWordPath y hk r).vertex (eastTick y hk r q).castSucc)
      ((heightWordPath y hk r).vertex (eastTick y hk r q).succ) =
      slot ⟨(r.val q).val, by have h := (y i).isLt; have hr := (r.val q).isLt; omega⟩ := by
  let t := eastTick y hk r q
  have ht : t.val = eastTime (hallSource j) r.val q := rfl
  have hs : hallSource j < t.val := by rw [ht]; unfold eastTime; omega
  have he : t.val < endpointTime y i := by
    have hq := q.isLt
    have hr := (r.val q).isLt
    rw [ht]
    unfold eastTime endpointTime
    omega
  obtain ⟨p, p', hp, hp', hx, hx', htime⟩ := active_edge_coordinates y (heightWordPath y hk r) t hs he
  rw [heightWordPath_horizontal y hk r _ (by omega) (by unfold endpointTime at he; omega),
    ht, thresholdHorizontal_before_east _ _ r.property] at hx
  rw [heightWordPath_horizontal y hk r _ (by omega) (by unfold endpointTime at he; omega),
    ht, thresholdHorizontal_at_east _ _ r.property] at hx'
  have hxp : p.1.val = hallSource j+q.val := by omega
  have hxq : p'.1.val = hallSource j+q.val+1 := by omega
  have hv : p.2 = (⟨(r.val q).val, by have h := (y i).isLt; have hr := (r.val q).isLt; omega⟩ : Fin (M+1)) := by
    apply Fin.ext
    change p.2.val = (r.val q).val
    rw [ht] at htime
    unfold eastTime at htime
    omega
  change edgeWeight slot t _ _ = _
  rw [hp, hp']
  simp only [edgeWeight, if_pos (show p.1.val+1 = p'.1.val by omega), hv]

theorem heightWord_noneastWeight (t : Fin (d+M+2))
    (hn : ∀ q, eastTick y hk r q ≠ t) :
    edgeWeight slot t ((heightWordPath y hk r).vertex t.castSucc)
      ((heightWordPath y hk r).vertex t.succ) = 1 := by
  by_cases hs : t.val ≤ hallSource j
  · exact inactive_edgeWeight y _ slot t (Or.inl hs)
  by_cases he : endpointTime y i ≤ t.val
  · exact inactive_edgeWeight y _ slot t (Or.inr he)
  have hstart : hallSource j < t.val := by omega
  have hend : t.val < endpointTime y i := by omega
  obtain ⟨p, q, hp, hq, hx, hx', _⟩ := active_edge_coordinates y (heightWordPath y hk r) t hstart hend
  rw [heightWordPath_horizontal y hk r _ (by omega) (by unfold endpointTime at hend; omega)] at hx
  rw [heightWordPath_horizontal y hk r _ (by omega) (by unfold endpointTime at hend; omega)] at hx'
  have heq := thresholdHorizontal_no_east (hallSource j) r.val t.val (by omega) (fun q he =>
    hn q (Fin.ext he))
  have hpq : p.1.val = q.1.val := by omega
  rw [hp, hq]
  simp only [edgeWeight, if_neg (show ¬p.1.val+1 = q.1.val by omega)]

theorem heightWord_weight :
    layeredPathWeight (edgeWeight slot) (heightWordPath y hk r) =
      ∏ q, slot ⟨(r.val q).val, by have h := (y i).isLt; have hr := (r.val q).isLt; omega⟩ := by
  classical
  let w := fun t => edgeWeight slot t ((heightWordPath y hk r).vertex t.castSucc)
    ((heightWordPath y hk r).vertex t.succ)
  change ∏ t, w t = _
  calc
    ∏ t, w t = ∏ t ∈ Finset.univ.image (eastTick y hk r), w t := by
      symm
      apply Finset.prod_subset (Finset.subset_univ _)
      intro t _ ht
      apply heightWord_noneastWeight y hk r slot t
      intro q hq
      exact ht (Finset.mem_image.mpr ⟨q, Finset.mem_univ _, hq⟩)
    _ = ∏ q, w (eastTick y hk r q) := Finset.prod_image (eastTick_injective y hk r).injOn
    _ = _ := by
      apply Finset.prod_congr rfl
      intro q _
      exact heightWord_eastWeight y hk r slot q

include hk in
theorem row_path_sum :
    (∑ P : LayeredPath (edges y) (start j) (finish i), layeredPathWeight (edgeWeight slot) P) =
      ∑ r : WeakHeights k (y i).val, ∏ q,
        slot ⟨(r.val q).val, by have h := (y i).isLt; have hr := (r.val q).isLt; omega⟩ := by
  classical
  rw [← Equiv.sum_comp (rowPathEquiv y hk) (layeredPathWeight (edgeWeight slot))]
  apply Finset.sum_congr rfl
  intro r _
  exact heightWord_weight y hk r slot

end
end Schubert.RS.HallLattice
