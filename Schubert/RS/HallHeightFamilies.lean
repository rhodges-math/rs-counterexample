import Schubert.RS.HallOneEastEquivalence

/-! Nonintersecting Hall families are precisely strict bounded height columns. -/

namespace Schubert.RS.HallLattice
noncomputable section
variable {d M : ℕ} (y : Fin d → Fin (M+1))

def heightFamily (r : ∀ i, Fin ((y i).val+1)) : LayeredPathFamily (edges y) start finish where
  matching := 1
  path i := (heightPath y i (r i)).vertex
  start i := (heightPath y i (r i)).start
  finish i := (heightPath y i (r i)).finish
  edges i := (heightPath y i (r i)).edges

theorem grid_active {j i : Fin d} (P : LayeredPath (edges y) (start j) (finish i))
    (t : Fin (d+M+3)) (p : Fin (d+1) × Fin (M+1))
    (hp : P.vertex t = .inr (.inl p)) :
    hallSource j < t.val ∧ t.val ≤ endpointTime y i := by
  constructor
  · by_contra hn
    rw [path_before_start y P t (by omega)] at hp
    simp only [start, Sum.inl_ne_inr] at hp
  · by_contra hn
    rw [path_after_finish y P t (by omega)] at hp
    simp only [finish, Sum.inr.injEq, Sum.inr_ne_inl] at hp

theorem heightFamily_disjoint_of_strict (r : ∀ i, Fin ((y i).val+1))
    (hr : StrictMono (fun i => (r i).val)) :
    ¬(pathCollisionTimes (heightFamily y r).path).Nonempty := by
  classical
  intro hc
  obtain ⟨t, ht⟩ := hc
  obtain ⟨z, hz⟩ := (mem_pathCollisionTimes _ _).mp ht
  simp only [pathCollisionPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hz
  obtain ⟨hij, he⟩ := hz
  let i := (ofLex z).1
  let j := (ofLex z).2
  change i < j at hij
  change (heightPath y i (r i)).vertex t = (heightPath y j (r j)).vertex t at he
  let P := heightPath y i (r i)
  let Q := heightPath y j (r j)
  change P.vertex t = Q.vertex t at he
  rcases hv : P.vertex t with k | p | k
  · have hi := path_start_label y P t k hv
    have hj := path_start_label y Q t k (he.symm.trans hv)
    exact (ne_of_lt hij) (hi.symm.trans hj)
  · have hq := he.symm.trans hv
    have hi := grid_active y P t p hv
    have hj := grid_active y Q t p hq
    have htpos : 1 ≤ t.val := by omega
    have hlocal : t.val-1+1 = t.val := Nat.sub_add_cancel htpos
    have htt : t.val-1+1 < d+M+3 := by rw [hlocal]; exact t.isLt
    have hpp : P.vertex ⟨t.val-1+1, htt⟩ = .inr (.inl p) := by
      convert hv using 1
      apply congrArg P.vertex
      exact Fin.ext hlocal
    have hqq : Q.vertex ⟨t.val-1+1, htt⟩ = .inr (.inl p) := by
      convert hq using 1
      apply congrArg Q.vertex
      exact Fin.ext hlocal
    have hx := (pathHorizontal_grid y P _ htt p hpp).trans
      (pathHorizontal_grid y Q _ htt p hqq).symm
    have hie : t.val-1 ≤ hallSource i+1+(y i).val := by
      unfold endpointTime at hi; omega
    have hje : t.val-1 ≤ hallSource j+1+(y j).val := by
      unfold endpointTime at hj; omega
    change pathHorizontal y (heightPath y i (r i)) _ =
      pathHorizontal y (heightPath y j (r j)) _ at hx
    rw [heightPath_horizontal y i _ _ (by omega) hie,
      heightPath_horizontal y j _ _ (by omega) hje] at hx
    exact strictMono_oneEastFamilyDisjoint (fun i => (y i).val) (fun i => (r i).val) hr
      i j hij ⟨t.val-1, by omega, by omega, hie, hje, hx⟩
  · have hi := path_finish_label y P t k hv
    have hj := path_finish_label y Q t k (he.symm.trans hv)
    exact (ne_of_lt hij) (hi.symm.trans hj)

theorem heightFamily_strict_of_disjoint (hy : Monotone (fun i => (y i).val))
    (r : ∀ i, Fin ((y i).val+1))
    (hr : ¬(pathCollisionTimes (heightFamily y r).path).Nonempty) :
    StrictMono (fun i => (r i).val) := by
  apply (oneEastFamilyDisjoint_iff_strictMono (fun i => (y i).val)
    (fun i => (r i).val) hy (fun i => by have h := (r i).isLt; omega)).mp
  intro i j hij
  rintro ⟨t, hi, hj, hie, hje, he⟩
  have hh : pathHorizontal y (heightPath y i (r i)) t =
      pathHorizontal y (heightPath y j (r j)) t := by
    rw [heightPath_horizontal y i _ t hi hie, heightPath_horizontal y j _ t hj hje]
    exact he
  obtain ⟨z, hz⟩ := horizontal_intersection_is_vertex_intersection y
    (heightPath y i (r i)) (heightPath y j (r j)) t hi hj hie hje hh
  exact no_path_collision_at (heightFamily y r).path hr i j (ne_of_lt hij) z hz

end
end Schubert.RS.HallLattice
