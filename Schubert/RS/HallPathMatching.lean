import Schubert.RS.HallPathDecode

/-! Ordered endpoints force identity matching in the actual finite Hall graph. -/

namespace Schubert.RS
noncomputable section

theorem no_path_collision_at {V : Type*} {d T : ℕ}
    (p : Fin d → Fin (T+1) → V) (hp : ¬(pathCollisionTimes p).Nonempty)
    (i j : Fin d) (hij : i ≠ j) (t : Fin (T+1)) : p i t ≠ p j t := by
  classical
  intro he
  have hlt (a b : Fin d) (hab : a < b) (heq : p a t = p b t) : False := by
    apply hp
    refine ⟨t, (mem_pathCollisionTimes p t).mpr ?_⟩
    refine ⟨toLex (a,b), ?_⟩
    simp [pathCollisionPairs, hab, heq]
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt i j h he
  · exact hlt j i h he.symm

namespace HallLattice
variable {d M : ℕ} (y : Fin d → Fin (M+1))

theorem horizontal_intersection_is_vertex_intersection
    {j k i l : Fin d}
    (P : LayeredPath (edges y) (start j) (finish i))
    (Q : LayeredPath (edges y) (start k) (finish l))
    (t : ℕ) (hj : hallSource j ≤ t) (hk : hallSource k ≤ t)
    (hi : t ≤ hallSource i+1+(y i).val) (hl : t ≤ hallSource l+1+(y l).val)
    (he : pathHorizontal y P t = pathHorizontal y Q t) :
    ∃ z : Fin (d+M+3), P.vertex z = Q.vertex z := by
  have ht := active_tick_bound y t hi
  obtain ⟨p, hp⟩ := path_active_grid y P ⟨t+1, ht⟩ (by simp; omega) (by
    change t+1 ≤ endpointTime y i; unfold endpointTime; omega)
  obtain ⟨q, hq⟩ := path_active_grid y Q ⟨t+1, ht⟩ (by simp; omega) (by
    change t+1 ≤ endpointTime y l; unfold endpointTime; omega)
  rw [pathHorizontal_grid y P t ht p hp, pathHorizontal_grid y Q t ht q hq] at he
  have hx : p.1.val = q.1.val := by exact_mod_cast he
  have htp := path_vertex_time y j i P ⟨t+1, ht⟩
  have htq := path_vertex_time y k l Q ⟨t+1, ht⟩
  rw [hp] at htp
  rw [hq] at htq
  change t+1 = p.1.val+p.2.val+1 at htp
  change t+1 = q.1.val+q.2.val+1 at htq
  have hy : p.2.val = q.2.val := by omega
  have hpq : p = q := Prod.ext (Fin.ext hx) (Fin.ext hy)
  exact ⟨⟨t+1, ht⟩, hp.trans ((congrArg (fun p => Sum.inr (Sum.inl p)) hpq).trans hq.symm)⟩

def familyPath (P : LayeredPathFamily (edges y) start finish) (j : Fin d) :
    LayeredPath (edges y) (start j) (finish (P.matching j)) where
  vertex := P.path j
  start := P.start j
  finish := P.finish j
  edges := P.edges j

theorem hallSource_strictAnti (d : ℕ) : StrictAnti (@hallSource d) := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  have h : i.val < j.val := hij
  unfold hallSource
  omega

theorem nonintersecting_matching_identity
    (hy : Monotone (fun i => (y i).val))
    (P : LayeredPathFamily (edges y) start finish)
    (hp : ¬(pathCollisionTimes P.path).Nonempty) : P.matching = 1 := by
  apply ordered_lattice_matching hallSource (fun i => hallSource i+1)
    (fun i => (y i).val) (hallSource_strictAnti d)
    (fun i j hij => Nat.add_lt_add_right (hallSource_strictAnti d hij) 1) hy
    P.matching (fun j => decodedPath y (familyPath y P j))
  intro i j hij t hi hj hti htj he
  obtain ⟨z, hz⟩ := horizontal_intersection_is_vertex_intersection y
    (familyPath y P i) (familyPath y P j) t hi hj hti htj he
  exact no_path_collision_at P.path hp i j hij z hz

end HallLattice
end
end Schubert.RS
