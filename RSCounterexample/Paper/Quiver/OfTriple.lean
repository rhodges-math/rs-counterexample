import RSCounterexample.Paper.Quiver.Triple.Basic
import RSCounterexample.Paper.Quiver.Multiplicity
import TauCeti.RepresentationTheory.ClassicalGroups.DominantWeight

/-!
# The quiver of a quiver triple

For weak compositions `a, b, c`, `N ≥ max c` and an interval partition `I_0 < ⋯ < I_{s−1}` of
`{0, …, n − 1}`, the quiver `Q` of Theorem 5.3 of the paper has one vertex per interval, of
dimension `|I_p|`, and `k_{pq} = cmp((a_i, b_i, c̄_i), (a_j, b_j, c̄_j))` arrows `p → q` for
`p < q`, read at the first positions `i ∈ I_p`, `j ∈ I_q` (for a quiver partition the value does not
depend on the positions). The weight `λ^{(p)}` is the residual `ν = c − a − b` on `I_p`, listed
from the last position of `I_p` to the first.

## Main definitions

* `Schubert.RS.Quiver.quiverOf`: the quiver `Q`.
* `Schubert.RS.Quiver.leviWeight`: the weight `(λ^{(p)})_p`.
* `Schubert.RS.Quiver.leviDominantWeight`: the same weight as Tau Ceti dominant weights, for a
  quiver partition.

## Main results

* `Schubert.RS.Quiver.isDominant_leviWeight`: for a quiver partition, each `λ^{(p)}` is weakly
  decreasing.
* `Schubert.RS.Quiver.quiverOf_eq_of_le`: the quiver does not depend on `N ≥ max c`.
-/

namespace Schubert.RS.Quiver

variable {n : ℕ}

/-- **The quiver of Theorem 5.3**: one vertex per interval of `I`, of dimension the length of the
interval, and `cmp((a_i, b_i, c̄_i), (a_j, b_j, c̄_j))` arrows `p → q` for `p < q`, read at the
first positions of the two intervals. -/
abbrev quiverOf (a b c : Composition n) (N : ℕ) (I : IntervalPartition n) : ForwardQuiver where
  s := I.length
  dim := I.blocksFun
  arrows p q := if p < q then
    (Window.cmp (Window.triple a b (Window.complement N c) (I.first p))
      (Window.triple a b (Window.complement N c) (I.first q))).toNat else 0
  forward p q h := by
    by_contra hpq
    exact h (by simp only [hpq, ↓reduceIte])

/-- **The weight `(λ^{(p)})_p` of Theorem 5.3**: on the interval `I_p = {i_1 < ⋯ < i_d}`,
`λ^{(p)} = (ν_{i_d}, …, ν_{i_1})` with `ν = c − a − b`. -/
def leviWeight (a b c : Composition n) (I : IntervalPartition n) :
    (p : Fin I.length) → Fin (I.blocksFun p) → ℤ :=
  fun p k => Window.residual a b c (I.embedding p (Fin.rev k))

variable {a b c : Composition n} {N : ℕ} {I : IntervalPartition n}

theorem quiverOf_s : (quiverOf a b c N I).s = I.length := rfl

theorem quiverOf_dim : (quiverOf a b c N I).dim = I.blocksFun := rfl

theorem quiverOf_arrows (p q : Fin I.length) :
    (quiverOf a b c N I).arrows p q = if p < q then
      (Window.cmp (Window.triple a b (Window.complement N c) (I.first p))
        (Window.triple a b (Window.complement N c) (I.first q))).toNat else 0 := rfl

/-- For a quiver partition, `ν = c − a − b` is weakly increasing on every interval. -/
theorem IsQuiverPartition.residual_mono (h : IsQuiverPartition a b c N I) {i j : Fin n}
    (hij : i ≤ j) (hb : I.index i = I.index j) :
    Window.residual a b c i ≤ Window.residual a b c j := by
  obtain ⟨ha, hb', hc⟩ := h.antitone i j hij hb
  have hci := h.hyp.le_N i
  have hcj := h.hyp.le_N j
  simp only [Window.complement] at hc
  simp only [Window.residual]
  omega

/-- For a quiver partition, each `λ^{(p)}` is weakly decreasing: `λ` is a dominant weight of the
Levi subgroup. -/
theorem isDominant_leviWeight (h : IsQuiverPartition a b c N I) :
    (quiverOf a b c N I).IsDominant (leviWeight a b c I) := by
  intro p k l hkl
  apply h.residual_mono
  · exact (I.embedding p).monotone (Fin.rev_le_rev.mpr hkl)
  · exact (I.index_embedding p _).trans (I.index_embedding p _).symm

/-- The weights `λ^{(p)}` of a quiver partition as Tau Ceti dominant weights: the highest weights
of the irreducible representations `V_p^{λ^{(p)}}` of `GL(I_p)`. -/
def leviDominantWeight (h : IsQuiverPartition a b c N I) :
    (p : Fin I.length) → TauCeti.DominantWeight (I.blocksFun p) :=
  fun p => ⟨leviWeight a b c I p, isDominant_leviWeight h p⟩

/-- The quiver does not depend on the choice of `N ≥ max c`. -/
theorem quiverOf_eq_of_le (hN : ∀ i, c i ≤ N) {N' : ℕ} (hN' : ∀ i, c i ≤ N') :
    quiverOf a b c N I = quiverOf a b c N' I := by
  unfold quiverOf
  congr 1
  funext p q
  rw [Window.cmp_complement_eq a b hN hN']

/-- For a quiver partition, the comparison weight between positions in intervals `p < q` is the
number of arrows `p → q`. -/
theorem IsQuiverPartition.cmp_eq_arrows (h : IsQuiverPartition a b c N I) {p q : Fin I.length}
    (hpq : p < q) (k : Fin (I.blocksFun p)) (l : Fin (I.blocksFun q)) :
    Window.cmp (Window.triple a b (Window.complement N c) (I.embedding p k))
      (Window.triple a b (Window.complement N c) (I.embedding q l)) =
      (quiverOf a b c N I).arrows p q := by
  obtain ⟨m, hm⟩ := h.cmp_const p q hpq
  rw [quiverOf_arrows]
  simp only [hpq, ↓reduceIte, IntervalPartition.first]
  rw [hm _ _ (I.index_embedding _ _) (I.index_embedding _ _),
    hm _ _ (I.index_embedding _ _) (I.index_embedding _ _)]
  simp

end Schubert.RS.Quiver
