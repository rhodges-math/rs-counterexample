import Schubert.RS.HallOneEastEquivalence

/-! Every identity path has exactly one weighted edge, its east step. -/

namespace Schubert.RS.HallLattice
noncomputable section
variable {d M : ℕ} (y : Fin d → Fin (M+1)) (i : Fin d)
variable {R : Type*} [CommRing R] (slot : Fin (M+1) → R)

theorem heightPath_edgeWeight (r : Fin ((y i).val+1)) (k : Fin (d+M+2)) :
    edgeWeight slot k ((heightPath y i r).vertex k.castSucc)
      ((heightPath y i r).vertex k.succ) =
      if k.val = hallSource i+r.val+1 then slot ⟨r.val, by have h := (y i).isLt; omega⟩ else 1 := by
  classical
  let P := heightPath y i r
  change edgeWeight slot k (P.vertex k.castSucc) (P.vertex k.succ) = _
  have hr := r.isLt
  by_cases hs : k.val ≤ hallSource i
  · rw [path_before_start y P k.castSucc hs]
    simp only [edgeWeight, start, if_neg (show k.val ≠ hallSource i+r.val+1 by omega)]
  · by_cases he : endpointTime y i ≤ k.val
    · rw [path_after_finish y P k.succ (by change endpointTime y i < k.val+1; omega)]
      have hn : k.val ≠ hallSource i+r.val+1 := by unfold endpointTime at he; omega
      simp only [if_neg hn]
      cases P.vertex k.castSucc with
      | inl j => rfl
      | inr p => cases p <;> rfl
    · have hks : hallSource i < k.val := by omega
      have hke : k.val < endpointTime y i := by omega
      obtain ⟨p, hp⟩ := path_active_grid y P k.castSucc hks (by change k.val ≤ endpointTime y i; omega)
      obtain ⟨q, hq⟩ := path_active_grid y P k.succ (by change hallSource i < k.val+1; omega)
        (by change k.val+1 ≤ endpointTime y i; omega)
      rw [hp, hq]
      have hkpos : 1 ≤ k.val := by omega
      have hklocal : k.val-1+1 = k.val := Nat.sub_add_cancel hkpos
      have ht : k.val-1+1 < d+M+3 := by rw [hklocal]; omega
      have hp' : P.vertex ⟨k.val-1+1, ht⟩ = .inr (.inl p) := by
        convert hp using 1
        apply congrArg P.vertex
        exact Fin.ext hklocal
      have hx := pathHorizontal_grid y P (k.val-1) ht p hp'
      have hx' := pathHorizontal_grid y P k.val (by have h := k.isLt; omega) q hq
      change pathHorizontal y (heightPath y i r) _ = _ at hx hx'
      rw [heightPath_horizontal y i r _ (by omega) (by unfold endpointTime at hke; omega)] at hx
      rw [heightPath_horizontal y i r _ (by omega) (by unfold endpointTime at hke; omega)] at hx'
      have htime := path_vertex_time y i i P k.castSucc
      rw [hp] at htime
      change k.val = p.1.val+p.2.val+1 at htime
      by_cases heq : k.val = hallSource i+r.val+1
      · have hxp : p.1.val = hallSource i := by
          simp only [oneEastHorizontal, if_pos (show k.val-1 ≤ hallSource i+r.val by omega)] at hx
          omega
        have hxq : q.1.val = hallSource i+1 := by
          simp only [oneEastHorizontal, if_neg (show ¬k.val ≤ hallSource i+r.val by omega)] at hx'
          omega
        have hv : p.2 = (⟨r.val, by have h := (y i).isLt; omega⟩ : Fin (M+1)) :=
          Fin.ext (by change p.2.val = r.val; omega)
        simp only [edgeWeight, if_pos (show p.1.val+1 = q.1.val by omega), if_pos heq, hv]
      · have hne : p.1.val+1 ≠ q.1.val := by
          unfold oneEastHorizontal at hx hx'
          split_ifs at hx <;> split_ifs at hx' <;> omega
        simp only [edgeWeight, if_neg hne, if_neg heq]

theorem heightPath_weight (r : Fin ((y i).val+1)) :
    layeredPathWeight (edgeWeight slot) (heightPath y i r) =
      slot ⟨r.val, by have h := (y i).isLt; omega⟩ := by
  classical
  have hb : hallSource i+r.val+1 < d+M+2 := by
    have hs := source_bound i
    have hr := r.isLt
    have hy := (y i).isLt
    omega
  let k : Fin (d+M+2) := ⟨hallSource i+r.val+1, hb⟩
  unfold layeredPathWeight
  simp_rw [heightPath_edgeWeight]
  rw [Finset.prod_eq_single k]
  · simp only [k, if_true]
  · intro j _ hj
    apply if_neg
    intro he
    exact hj (Fin.ext he)
  · simp

end
end Schubert.RS.HallLattice
