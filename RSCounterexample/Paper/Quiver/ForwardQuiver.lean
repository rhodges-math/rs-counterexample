import RSCounterexample.Paper.Quiver.LeviShape

/-!
# Forward quivers

A quiver without oriented cycles, with its vertices listed in a topological order `0, …, s − 1`,
so that every arrow `p → q` has `p < q`, together with a dimension vector. Parallel arrows are
allowed and are distinct.

## Main definitions

* `Schubert.RS.Quiver.ForwardQuiver`: the data `(s, dim, arrows)`.
* `Schubert.RS.Quiver.ForwardQuiver.Arrow`: the arrows, as a finite type.
* `Schubert.RS.Quiver.ForwardQuiver.Weight`, `IsDominant`: weights of `∏_p GL(dim p)`; dominant
  means weakly decreasing on each vertex.
-/

namespace Schubert.RS.Quiver

/-- A quiver whose arrows all point forward (an acyclic quiver with its vertices in a topological
order), with a dimension vector. `arrows p q` is the number of arrows `p → q`. -/
structure ForwardQuiver where
  /-- The number of vertices. -/
  s : ℕ
  /-- The dimension vector. -/
  dim : Fin s → ℕ
  /-- The number of arrows `p → q`. -/
  arrows : Fin s → Fin s → ℕ
  /-- Every arrow points forward. -/
  forward : ∀ p q, arrows p q ≠ 0 → p < q

namespace ForwardQuiver

variable (Q : ForwardQuiver)

/-- The number of variables `∑_p dim p`. -/
abbrev n : ℕ := Levi.total Q.dim

/-- The arrows of `Q`: an arrow is a pair of vertices `(p, q)` and an index among the parallel
arrows `p → q`. -/
abbrev Arrow : Type := Σ pq : Fin Q.s × Fin Q.s, Fin (Q.arrows pq.1 pq.2)

/-- The source of an arrow. -/
def src (e : Q.Arrow) : Fin Q.s := e.1.1

/-- The target of an arrow. -/
def tgt (e : Q.Arrow) : Fin Q.s := e.1.2

theorem src_lt_tgt (e : Q.Arrow) : Q.src e < Q.tgt e :=
  Q.forward _ _ fun h => (Fin.elim0 (h ▸ e.2))

/-- Weights of `∏_p GL(dim p)`: one integer vector per vertex. -/
abbrev Weight : Type := (p : Fin Q.s) → Fin (Q.dim p) → ℤ

/-- A weight is dominant when it is weakly decreasing on each vertex. -/
def IsDominant (lam : Q.Weight) : Prop := ∀ p, Antitone (lam p)

/-- The position of the `i`-th variable of vertex `p`. -/
abbrev pos (p : Fin Q.s) (i : Fin (Q.dim p)) : Fin Q.n := Levi.pos Q.dim p i

theorem IsDominant.smul {Q : ForwardQuiver} {lam : Q.Weight} (h : Q.IsDominant lam) (N : ℕ) :
    Q.IsDominant (N • lam) := fun p i j hij => by
  simp only [Pi.smul_apply]
  exact nsmul_le_nsmul_right (h p hij) N

end ForwardQuiver

end Schubert.RS.Quiver
