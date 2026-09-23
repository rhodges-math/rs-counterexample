import Schubert.RS.PathTailSwap
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max

/-! The first-intersection choice in the Hall-path tail involution. -/

namespace Schubert.RS
noncomputable section
variable {V : Type*} {d T : ℕ}

def pathCollisionPairs (p : Fin d → Fin (T + 1) → V) (t : Fin (T + 1)) :
    Finset (Fin d ×ₗ Fin d) := by
  classical
  exact Finset.univ.filter (fun z => (ofLex z).1 < (ofLex z).2 ∧
    p (ofLex z).1 t = p (ofLex z).2 t)

def pathCollisionTimes (p : Fin d → Fin (T + 1) → V) : Finset (Fin (T + 1)) := by
  classical
  exact Finset.univ.filter (fun t => (pathCollisionPairs p t).Nonempty)

@[simp] theorem mem_pathCollisionTimes (p : Fin d → Fin (T + 1) → V) (t : Fin (T + 1)) :
    t ∈ pathCollisionTimes p ↔ (pathCollisionPairs p t).Nonempty := by
  classical
  simp [pathCollisionTimes]

theorem pathCollisionPairs_prefix (p : Fin d → Fin (T + 1) → V)
    (t k : Fin (T + 1)) (a b : Fin d) (hk : k ≤ t) :
    pathCollisionPairs (swapPathTails p t a b) k = pathCollisionPairs p k := by
  classical
  ext z
  simp [pathCollisionPairs, swapPathTails, hk]

def firstPathIntersection (p : Fin d → Fin (T + 1) → V)
    (hp : (pathCollisionTimes p).Nonempty) : Fin (T + 1) :=
  (pathCollisionTimes p).min' hp

theorem firstPathIntersection_mem (p : Fin d → Fin (T + 1) → V)
    (hp : (pathCollisionTimes p).Nonempty) :
    firstPathIntersection p hp ∈ pathCollisionTimes p :=
  Finset.min'_mem _ _

theorem swapPathTails_collision_nonempty (p : Fin d → Fin (T + 1) → V)
    (hp : (pathCollisionTimes p).Nonempty) (a b : Fin d) :
    (pathCollisionTimes (swapPathTails p (firstPathIntersection p hp) a b)).Nonempty := by
  refine ⟨firstPathIntersection p hp, ?_⟩
  rw [mem_pathCollisionTimes, pathCollisionPairs_prefix p _ _ a b le_rfl]
  exact (mem_pathCollisionTimes _ _).mp (firstPathIntersection_mem p hp)

/-- Strict tails cannot change either the chosen first time or any earlier
collision data. This is the non-circular part of the involution argument. -/
theorem firstPathIntersection_swap (p : Fin d → Fin (T + 1) → V)
    (hp : (pathCollisionTimes p).Nonempty) (a b : Fin d) :
    firstPathIntersection (swapPathTails p (firstPathIntersection p hp) a b)
      (swapPathTails_collision_nonempty p hp a b) = firstPathIntersection p hp := by
  let q := swapPathTails p (firstPathIntersection p hp) a b
  have ht : firstPathIntersection p hp ∈ pathCollisionTimes q := by
    rw [mem_pathCollisionTimes]
    change (pathCollisionPairs (swapPathTails p (firstPathIntersection p hp) a b) _).Nonempty
    rw [pathCollisionPairs_prefix p _ _ a b le_rfl]
    exact (mem_pathCollisionTimes _ _).mp (firstPathIntersection_mem p hp)
  have hle : firstPathIntersection q (swapPathTails_collision_nonempty p hp a b) ≤
      firstPathIntersection p hp := Finset.min'_le _ _ ht
  apply le_antisymm hle
  apply Finset.min'_le
  rw [mem_pathCollisionTimes]
  rw [← pathCollisionPairs_prefix p _ _ a b hle]
  exact (mem_pathCollisionTimes _ _).mp (firstPathIntersection_mem q _)

def firstPathPair (p : Fin d → Fin (T + 1) → V)
    (hp : (pathCollisionTimes p).Nonempty) : Fin d ×ₗ Fin d :=
  (pathCollisionPairs p (firstPathIntersection p hp)).min'
    ((mem_pathCollisionTimes _ _).mp (firstPathIntersection_mem p hp))

theorem firstPathPair_spec (p : Fin d → Fin (T + 1) → V)
    (hp : (pathCollisionTimes p).Nonempty) :
    (ofLex (firstPathPair p hp)).1 < (ofLex (firstPathPair p hp)).2 ∧
      p (ofLex (firstPathPair p hp)).1 (firstPathIntersection p hp) =
      p (ofLex (firstPathPair p hp)).2 (firstPathIntersection p hp) := by
  classical
  have h := Finset.min'_mem (pathCollisionPairs p (firstPathIntersection p hp))
    ((mem_pathCollisionTimes _ _).mp (firstPathIntersection_mem p hp))
  simpa only [firstPathPair, pathCollisionPairs, Finset.mem_filter, Finset.mem_univ, true_and] using h

theorem firstPathPair_swap (p : Fin d → Fin (T + 1) → V)
    (hp : (pathCollisionTimes p).Nonempty) (a b : Fin d) :
    firstPathPair (swapPathTails p (firstPathIntersection p hp) a b)
      (swapPathTails_collision_nonempty p hp a b) = firstPathPair p hp := by
  unfold firstPathPair
  simp only [firstPathIntersection_swap]
  simp only [pathCollisionPairs_prefix p _ _ a b le_rfl]

/-- The deterministic tail exchange: first diagonal time, then first ordered
pair of labels. All vertices at the chosen time are unchanged by exchange. -/
def exchangeFirstPathTails (p : Fin d → Fin (T + 1) → V)
    (hp : (pathCollisionTimes p).Nonempty) : Fin d → Fin (T + 1) → V :=
  swapPathTails p (firstPathIntersection p hp)
    (ofLex (firstPathPair p hp)).1 (ofLex (firstPathPair p hp)).2

theorem exchangeFirstPathTails_nonempty (p : Fin d → Fin (T + 1) → V)
    (hp : (pathCollisionTimes p).Nonempty) :
    (pathCollisionTimes (exchangeFirstPathTails p hp)).Nonempty :=
  swapPathTails_collision_nonempty p hp _ _

theorem exchangeFirstPathTails_involutive (p : Fin d → Fin (T + 1) → V)
    (hp : (pathCollisionTimes p).Nonempty) :
    exchangeFirstPathTails (exchangeFirstPathTails p hp)
      (exchangeFirstPathTails_nonempty p hp) = p := by
  unfold exchangeFirstPathTails
  rw [firstPathIntersection_swap, firstPathPair_swap]
  exact swapPathTails_involutive p _ _ _

theorem exchangeFirstPathTails_weight {R : Type*} [CommMonoid R]
    (p : Fin d → Fin (T + 1) → V) (hp : (pathCollisionTimes p).Nonempty)
    (w : Fin T → V → V → R) :
    (∏ k, ∏ i, w k (exchangeFirstPathTails p hp i k.castSucc)
      (exchangeFirstPathTails p hp i k.succ)) = ∏ k, ∏ i, w k (p i k.castSucc) (p i k.succ) :=
  swapPathTails_weight p _ _ _ (firstPathPair_spec p hp).2 w

end
end Schubert.RS
