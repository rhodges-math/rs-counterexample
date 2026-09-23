import Schubert.RS.PathDeterminant
import Schubert.RS.OneEastFamilies

/-!
Finite padding of the north/east lattice in the paper's Hall proof. Private
source and sink vertices put all paths on a common time interval without
introducing intersections. Heights here are shifted down by one.
-/

namespace Schubert.RS.HallLattice
noncomputable section
variable {d M : ℕ}

abbrev Vertex (d M : ℕ) := Fin d ⊕ ((Fin (d+1) × Fin (M+1)) ⊕ Fin d)

def start (j : Fin d) : Vertex d M := .inl j
def finish (i : Fin d) : Vertex d M := .inr (.inr i)

def endpointTime (y : Fin d → Fin (M+1)) (i : Fin d) : ℕ :=
  hallSource i + y i + 2

def edges (y : Fin d → Fin (M+1)) (t : Fin (d+M+2)) : Vertex d M → Vertex d M → Prop
  | .inl j, .inl k => j = k ∧ t.val < hallSource j
  | .inl j, .inr (.inl p) => t.val = hallSource j ∧ p.1.val = hallSource j ∧ p.2.val = 0
  | .inr (.inl p), .inr (.inl q) =>
      (q.1.val = p.1.val+1 ∧ q.2 = p.2) ∨ (q.1 = p.1 ∧ q.2.val = p.2.val+1)
  | .inr (.inl p), .inr (.inr i) =>
      t.val = endpointTime y i ∧ p.1.val = hallSource i+1 ∧ p.2 = y i
  | .inr (.inr i), .inr (.inr j) => i = j
  | _, _ => False

def vertexAt (y : Fin d → Fin (M+1)) (t : ℕ) : Vertex d M → Prop
  | .inl j => t ≤ hallSource j
  | .inr (.inl p) => t = p.1.val+p.2.val+1
  | .inr (.inr i) => endpointTime y i+1 ≤ t

theorem finish_injective : Function.Injective (finish : Fin d → Vertex d M) := by
  intro i j h
  exact Sum.inr.inj (Sum.inr.inj h)

theorem source_bound (i : Fin d) : hallSource i < d := by
  have hi := i.isLt
  unfold hallSource
  omega

theorem endpoint_bound (y : Fin d → Fin (M+1)) (i : Fin d) :
    endpointTime y i+1 ≤ d+M+2 := by
  have hs := source_bound i
  have hy := (y i).isLt
  unfold endpointTime
  omega

theorem edge_preserves_time (y : Fin d → Fin (M+1)) (t : Fin (d+M+2))
    (v w : Vertex d M) (hv : vertexAt y t.val v) (he : edges y t v w) :
    vertexAt y (t.val+1) w := by
  rcases v with j | p | i <;> rcases w with k | q | l <;>
    simp only [vertexAt, edges] at hv he ⊢
  · obtain ⟨rfl, h⟩ := he
    omega
  · obtain ⟨ht, hx, hy⟩ := he
    omega
  · rcases he with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · rw [hy]
      omega
    · rw [hx]
      omega
  · obtain ⟨ht, hx, hy⟩ := he
    omega
  · subst l
    omega

theorem path_vertex_time (y : Fin d → Fin (M+1)) (j i : Fin d)
    (P : LayeredPath (edges y) (start j) (finish i))
    (t : Fin (d+M+3)) : vertexAt y t.val (P.vertex t) := by
  induction t using Fin.induction with
  | zero => rw [P.start]; exact Nat.zero_le _
  | succ t ih => exact edge_preserves_time y t _ _ ih (P.edges t)

def edgeWeight {R : Type*} [CommRing R] (slot : Fin (M+1) → R)
    (_t : Fin (d+M+2)) : Vertex d M → Vertex d M → R
  | .inr (.inl p), .inr (.inl q) => if p.1.val+1 = q.1.val then slot p.2 else 1
  | _, _ => 1

/-- All paths and all endpoint matchings are retained before cancellation. -/
theorem determinant_eq_disjoint_sum {R : Type*} [CommRing R]
    (y : Fin d → Fin (M+1)) (slot : Fin (M+1) → R) :
    Matrix.det (fun i j : Fin d =>
      ∑ P : LayeredPath (edges y) (start j) (finish i), layeredPathWeight (edgeWeight slot) P) =
      ∑ P : {P : LayeredPathFamily (edges y) start finish //
        ¬(pathCollisionTimes P.path).Nonempty}, pathFamilyWeight (edgeWeight slot) P.val :=
  determinant_nonintersecting_paths (edgeWeight slot) finish_injective

end
end Schubert.RS.HallLattice
