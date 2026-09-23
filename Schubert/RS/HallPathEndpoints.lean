import Schubert.RS.HallPathPhases

/-! Recover the actual source and endpoint of each padded Hall path. -/

namespace Schubert.RS.HallLattice
noncomputable section
variable {d M : ℕ} (y : Fin d → Fin (M+1))

def sourcePoint (j : Fin d) : Fin (d+1) × Fin (M+1) :=
  (⟨hallSource j, Nat.lt_succ_of_lt (source_bound j)⟩, 0)

def endpoint (i : Fin d) : Fin (d+1) × Fin (M+1) :=
  (⟨hallSource i+1, by have h := source_bound i; omega⟩, y i)

def sourceTick (j : Fin d) : Fin (d+M+2) :=
  ⟨hallSource j, by have h := source_bound j; omega⟩

def endpointTick (i : Fin d) : Fin (d+M+2) :=
  ⟨endpointTime y i, by have h := endpoint_bound y i; omega⟩

variable {j i : Fin d} (P : LayeredPath (edges y) (start j) (finish i))

theorem path_source_point :
    P.vertex (sourceTick (M := M) j).succ = .inr (.inl (sourcePoint j)) := by
  have he := P.edges (sourceTick (M := M) j)
  have hp := path_before_start y P (sourceTick (M := M) j).castSucc (by rfl)
  rw [hp] at he
  rcases hv : P.vertex (sourceTick (M := M) j).succ with k | p | l <;>
    rw [hv] at he <;> simp only [edges, start, sourceTick] at he
  · omega
  · apply congrArg (fun p => Sum.inr (Sum.inl p))
    exact Prod.ext (Fin.ext he.2.1) (Fin.ext he.2.2)

theorem path_endpoint :
    P.vertex (endpointTick y i).castSucc = .inr (.inl (endpoint y i)) := by
  have he := P.edges (endpointTick y i)
  have hn := path_after_finish y P (endpointTick y i).succ (by
    change endpointTime y i < endpointTime y i+1; omega)
  rw [hn] at he
  have ht := path_vertex_time y j i P (endpointTick y i).castSucc
  rcases hv : P.vertex (endpointTick y i).castSucc with k | p | l <;>
    rw [hv] at he ht <;> simp only [edges, finish, vertexAt, endpointTick] at he ht
  · apply congrArg (fun p => Sum.inr (Sum.inl p))
    exact Prod.ext (Fin.ext he.2.1) he.2.2
  · subst l
    change endpointTime y i+1 ≤ endpointTime y i at ht
    omega

include P in
theorem path_active_nonempty : hallSource j ≤ hallSource i+1+(y i).val := by
  by_contra hn
  have hs := path_source_point y P
  have ht : endpointTime y i < (sourceTick (M := M) j).succ.val := by
    simp only [endpointTime, sourceTick, Fin.val_succ]
    omega
  have hp := path_after_finish y P (sourceTick (M := M) j).succ ht
  rw [hs] at hp
  cases hp

end
end Schubert.RS.HallLattice
