import Schubert.RS.Quiver.Polytope.Flat
import Schubert.RS.Quiver.Decomposition

/-!
# The factors at a vertex as positional slots

Positional data `P` (`Schubert.RS.Quiver.Flat.PositionalQuiver`) *realizes* a forward quiver `Q`
with weight `λ` when the vertices `p` of `Q` sit at increasing positions `st p`, the starting
positions of `P`, with the dimensions, arrow numbers (at most two) and weights of `Q`.

The factors at a vertex `p` (`Schubert.RS.Quiver.ForwardQuiver.vertexFactors`: the outgoing arrows
by target and number, then the incoming arrows by source and number) are then the slots `(j, k)`
of `P` at the position `st p`: the arrow between `st p` and the position `j`, numbered `k`. The
factor `t` sits at the slot `(slotJ p t, slotK p t)`. This is a bijection onto the slots used by
`P` (`Schubert.RS.Quiver.Flat.PositionalQuiver.Realizes.sum_slots`), and it carries the order of
the factors to the order `slotBefore` of the slots
(`Schubert.RS.Quiver.Flat.PositionalQuiver.Realizes.lt_iff_slotBefore`).

## Main definitions

* `Schubert.RS.Quiver.ForwardQuiver.vertexArrows`, `Schubert.RS.Quiver.ForwardQuiver.arrowAt`: the
  arrows of the factors at a vertex.
* `Schubert.RS.Quiver.Flat.PositionalQuiver.Realizes`: positional data of a quiver with weight.
* `Schubert.RS.Quiver.Flat.PositionalQuiver.Realizes.slotJ`, `slotK`: the slot of a factor.

## Main results

* `Schubert.RS.Quiver.ForwardQuiver.vertexFactors_eq`: the factor of an outgoing or incoming arrow.
* `Schubert.RS.Quiver.Flat.PositionalQuiver.Realizes.outSlot_slot`, `inSlot_slot`.
* `Schubert.RS.Quiver.Flat.PositionalQuiver.Realizes.lt_iff_slotBefore`.
* `Schubert.RS.Quiver.Flat.PositionalQuiver.Realizes.sum_slots`.
-/

namespace Schubert.RS.Quiver

namespace ForwardQuiver

variable (Q : ForwardQuiver)

/-- The arrows at a vertex in the order of its factors: the outgoing arrows, then the incoming
ones. -/
def vertexArrows (p : Fin Q.s) : List Q.Arrow := Q.outArrows p ++ Q.inArrows p

theorem length_vertexArrows (p : Fin Q.s) : (Q.vertexArrows p).length = Q.valence p := by
  simp [vertexArrows, valence]

theorem nodup_vertexArrows (p : Fin Q.s) : (Q.vertexArrows p).Nodup := by
  rw [vertexArrows, List.nodup_append]
  refine ⟨Q.nodup_outArrows p, Q.nodup_inArrows p, fun e he e' he' hee' => ?_⟩
  rw [mem_outArrows] at he
  rw [mem_inArrows] at he'
  subst hee'
  have := Q.src_lt_tgt e
  rw [he, he'] at this
  exact lt_irrefl _ this

/-- The arrow of the factor `t` at the vertex `p`. -/
def arrowAt (p : Fin Q.s) (t : Fin (Q.valence p)) : Q.Arrow :=
  (Q.vertexArrows p)[t.1]'(by rw [length_vertexArrows]; exact t.isLt)

theorem arrowAt_mem (p : Fin Q.s) (t : Fin (Q.valence p)) : Q.arrowAt p t ∈ Q.vertexArrows p :=
  List.getElem_mem _

theorem src_eq_or_tgt_eq (p : Fin Q.s) (t : Fin (Q.valence p)) :
    Q.src (Q.arrowAt p t) = p ∨ Q.tgt (Q.arrowAt p t) = p := by
  have h := Q.arrowAt_mem p t
  rw [vertexArrows, List.mem_append, mem_outArrows, mem_inArrows] at h
  exact h

theorem tgt_eq_of_src_ne {p : Fin Q.s} {t : Fin (Q.valence p)} (h : Q.src (Q.arrowAt p t) ≠ p) :
    Q.tgt (Q.arrowAt p t) = p :=
  (Q.src_eq_or_tgt_eq p t).resolve_left h

theorem arrowAt_injective (p : Fin Q.s) : Function.Injective (Q.arrowAt p) := by
  intro t t' h
  have := (Q.nodup_vertexArrows p).getElem_inj_iff.mp h
  exact Fin.ext this

theorem exists_arrowAt {p : Fin Q.s} {e : Q.Arrow} (he : Q.src e = p ∨ Q.tgt e = p) :
    ∃ t, Q.arrowAt p t = e := by
  have hm : e ∈ Q.vertexArrows p := by
    rw [vertexArrows, List.mem_append, mem_outArrows, mem_inArrows]
    exact he
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hm
  exact ⟨⟨i, by rwa [← length_vertexArrows]⟩, rfl⟩

theorem arrowAt_of_lt {p : Fin Q.s} {t : Fin (Q.valence p)} (h : t.1 < (Q.outArrows p).length) :
    Q.arrowAt p t = (Q.outArrows p)[t.1] :=
  List.getElem_append_left h

theorem arrowAt_of_ge {p : Fin Q.s} {t : Fin (Q.valence p)} (h : (Q.outArrows p).length ≤ t.1) :
    Q.arrowAt p t = (Q.inArrows p)[t.1 - (Q.outArrows p).length]'(by
      have := t.isLt
      simp only [valence] at this
      omega) :=
  List.getElem_append_right h

theorem lt_length_outArrows_iff (p : Fin Q.s) (t : Fin (Q.valence p)) :
    t.1 < (Q.outArrows p).length ↔ Q.src (Q.arrowAt p t) = p := by
  constructor
  · intro h
    rw [Q.arrowAt_of_lt h, ← mem_outArrows]
    exact List.getElem_mem _
  · intro h
    by_contra hlt
    have h2 : Q.tgt (Q.arrowAt p t) = p := by
      rw [Q.arrowAt_of_ge (not_lt.mp hlt), ← mem_inArrows]
      exact List.getElem_mem _
    have := Q.src_lt_tgt (Q.arrowAt p t)
    rw [h, h2] at this
    exact lt_irrefl _ this

/-- **The factor of an arrow at a vertex**: `s_{μ_e}` for an outgoing arrow, and
`det^{−μ_{e,0}} s_{μ_e^c}` for an incoming one. -/
theorem vertexFactors_eq (μ : Q.ArrowShapes) (p : Fin Q.s) (t : Fin (Q.valence p)) :
    Q.vertexFactors μ p t =
      if Q.src (Q.arrowAt p t) = p then outFactor (μ (Q.arrowAt p t)).1
      else inFactor (Q.dim p) (μ (Q.arrowAt p t)).1 := by
  have hv : Q.vertexFactors μ p t = ((Q.outArrows p).map (fun e => outFactor (μ e).1) ++
      (Q.inArrows p).map fun e => inFactor (Q.dim p) (μ e).1)[t.1]'(by
        have := t.isLt
        simp only [valence] at this
        simpa using this) := rfl
  rw [hv]
  by_cases h : t.1 < (Q.outArrows p).length
  · rw [ite_eq_left ((Q.lt_length_outArrows_iff p t).mp h), Q.arrowAt_of_lt h]
    simp [h]
  · rw [ite_eq_right (fun h' => h ((Q.lt_length_outArrows_iff p t).mpr h')),
      Q.arrowAt_of_ge (not_lt.mp h)]
    simp [List.getElem_append, h]

end ForwardQuiver

namespace Flat

open Finset

namespace PositionalQuiver

/-- **Positional data realizing a forward quiver with a weight.** The vertex `p` sits at the
position `st p`; the positions `st p` are increasing and are exactly the starting positions of
`P`; the dimensions, the numbers of arrows (at most two) and the weights agree; and `P` has no
arrows away from its starting positions. -/
structure Realizes (P : PositionalQuiver) (Q : ForwardQuiver) (lam : Q.Weight) where
  /-- The position of a vertex. -/
  st : Fin Q.s → ℕ
  st_strictMono : StrictMono st
  st_lt : ∀ p, st p < P.n
  isStart_iff : ∀ i < P.n, P.isStart i = true ↔ ∃ p, st p = i
  blockDim_st : ∀ p, P.blockDim (st p) = Q.dim p
  dim_le : ∀ p, Q.dim p ≤ P.n
  arrowCount_st : ∀ p q, P.arrowCount (st p) (st q) = Q.arrows p q
  exists_of_arrowCount_ne_zero : ∀ i < P.n, ∀ j < P.n, P.arrowCount i j ≠ 0 →
    ∃ p q, st p = i ∧ st q = j
  arrows_le_two : ∀ p q, Q.arrows p q ≤ 2
  weight_st : ∀ p (l : Fin (Q.dim p)), P.weight (st p) l = lam p l

namespace Realizes

variable {P : PositionalQuiver} {Q : ForwardQuiver} {lam : Q.Weight} (R : P.Realizes Q lam)

theorem st_injective : Function.Injective R.st := R.st_strictMono.injective

theorem st_lt_st {p q : Fin Q.s} : R.st p < R.st q ↔ p < q := R.st_strictMono.lt_iff_lt

/-- The position of the other end of an arrow at the vertex `p`. -/
def otherEnd (p : Fin Q.s) (e : Q.Arrow) : ℕ :=
  if Q.src e = p then R.st (Q.tgt e) else R.st (Q.src e)

/-- The position of the other end of the arrow of the factor `t` at `p`. -/
def slotJ (p : Fin Q.s) (t : Fin (Q.valence p)) : ℕ := R.otherEnd p (Q.arrowAt p t)

/-- The number of the arrow of the factor `t` at `p` among its parallel arrows. -/
def slotK (_R : P.Realizes Q lam) (p : Fin Q.s) (t : Fin (Q.valence p)) : ℕ :=
  (Q.arrowAt p t).2.1

theorem slotJ_lt (p : Fin Q.s) (t : Fin (Q.valence p)) : R.slotJ p t < P.n := by
  unfold slotJ otherEnd
  split_ifs
  exacts [R.st_lt _, R.st_lt _]

theorem slotK_lt (p : Fin Q.s) (t : Fin (Q.valence p)) : R.slotK p t < 2 :=
  lt_of_lt_of_le (Q.arrowAt p t).2.isLt (R.arrows_le_two _ _)

theorem st_lt_slotJ {p : Fin Q.s} {t : Fin (Q.valence p)} (h : Q.src (Q.arrowAt p t) = p) :
    R.st p < R.slotJ p t := by
  unfold slotJ otherEnd
  rw [ite_eq_left h, R.st_lt_st]
  exact lt_of_eq_of_lt h.symm (Q.src_lt_tgt _)

theorem slotJ_lt_st {p : Fin Q.s} {t : Fin (Q.valence p)} (h : Q.src (Q.arrowAt p t) ≠ p) :
    R.slotJ p t < R.st p := by
  unfold slotJ otherEnd
  rw [ite_eq_right h, R.st_lt_st]
  exact lt_of_lt_of_eq (Q.src_lt_tgt _) (Q.tgt_eq_of_src_ne h)

theorem arrows_eq_zero_of_le {p q : Fin Q.s} (h : q ≤ p) : Q.arrows p q = 0 := by
  by_contra hne
  exact absurd (Q.forward p q hne) (not_lt.mpr h)

theorem lt_arrowCount (e : Q.Arrow) :
    (e.2 : ℕ) < P.arrowCount (R.st (Q.src e)) (R.st (Q.tgt e)) := by
  rw [R.arrowCount_st]
  exact e.2.isLt

/-- The slot of an outgoing factor is an outgoing slot of `P`. -/
theorem outSlot_slot (p : Fin Q.s) (t : Fin (Q.valence p)) :
    P.outSlot (R.st p) (R.slotJ p t) (R.slotK p t) = decide (Q.src (Q.arrowAt p t) = p) := by
  unfold outSlot slotJ otherEnd slotK
  by_cases h : Q.src (Q.arrowAt p t) = p
  · rw [ite_eq_left h, decide_eq_true h, decide_eq_true_iff]
    have := R.lt_arrowCount (Q.arrowAt p t)
    rwa [h] at this
  · rw [ite_eq_right h, decide_eq_false h, decide_eq_false_iff_not, R.arrowCount_st,
      arrows_eq_zero_of_le (lt_of_lt_of_eq (Q.src_lt_tgt _) (Q.tgt_eq_of_src_ne h)).le]
    omega

/-- The slot of an incoming factor is an incoming slot of `P`. -/
theorem inSlot_slot (p : Fin Q.s) (t : Fin (Q.valence p)) :
    P.inSlot (R.st p) (R.slotJ p t) (R.slotK p t) = !decide (Q.src (Q.arrowAt p t) = p) := by
  unfold inSlot slotJ otherEnd slotK
  by_cases h : Q.src (Q.arrowAt p t) = p
  · rw [ite_eq_left h, decide_eq_true h, Bool.not_true, decide_eq_false_iff_not, R.arrowCount_st,
      arrows_eq_zero_of_le (lt_of_eq_of_lt h.symm (Q.src_lt_tgt _)).le]
    omega
  · rw [ite_eq_right h, decide_eq_false h, Bool.not_false, decide_eq_true_iff]
    have := R.lt_arrowCount (Q.arrowAt p t)
    rwa [Q.tgt_eq_of_src_ne h] at this

theorem slot_injective (p : Fin Q.s) {t t' : Fin (Q.valence p)} (hj : R.slotJ p t = R.slotJ p t')
    (hk : R.slotK p t = R.slotK p t') : t = t' := by
  apply Q.arrowAt_injective p
  have key : (Q.arrowAt p t).1 = (Q.arrowAt p t').1 := by
    by_cases h : Q.src (Q.arrowAt p t) = p <;> by_cases h' : Q.src (Q.arrowAt p t') = p
    · unfold slotJ otherEnd at hj
      rw [ite_eq_left h, ite_eq_left h'] at hj
      exact Prod.ext (h.trans h'.symm) (R.st_injective hj)
    · have := R.st_lt_slotJ h
      have := R.slotJ_lt_st h'
      omega
    · have := R.slotJ_lt_st h
      have := R.st_lt_slotJ h'
      omega
    · unfold slotJ otherEnd at hj
      rw [ite_eq_right h, ite_eq_right h'] at hj
      exact Prod.ext (R.st_injective hj)
        ((Q.tgt_eq_of_src_ne h).trans (Q.tgt_eq_of_src_ne h').symm)
  have hk' : ((Q.arrowAt p t).2 : ℕ) = (Q.arrowAt p t').2 := hk
  generalize Q.arrowAt p t = e at key hk' ⊢
  generalize Q.arrowAt p t' = e' at key hk' ⊢
  obtain ⟨pq, k⟩ := e
  obtain ⟨pq', k'⟩ := e'
  simp only at key
  subst key
  simp only at hk'
  rw [Fin.ext hk']

/-- Every slot used by `P` at `st p` is the slot of a factor at `p`. -/
theorem exists_slot (p : Fin Q.s) {j k : ℕ} (hj : j < P.n)
    (h : (P.outSlot (R.st p) j k || P.inSlot (R.st p) j k) = true) :
    ∃ t, R.slotJ p t = j ∧ R.slotK p t = k := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · unfold outSlot at h
    rw [decide_eq_true_iff] at h
    obtain ⟨-, q, -, rfl⟩ := R.exists_of_arrowCount_ne_zero _ (R.st_lt p) _ hj (by omega)
    rw [R.arrowCount_st] at h
    obtain ⟨t, ht⟩ := Q.exists_arrowAt (p := p) (e := ⟨(p, q), ⟨k, h⟩⟩) (Or.inl rfl)
    refine ⟨t, ?_, ?_⟩
    · unfold slotJ otherEnd
      rw [ht]
      exact ite_eq_left rfl
    · unfold slotK
      rw [ht]
  · unfold inSlot at h
    rw [decide_eq_true_iff] at h
    obtain ⟨q, -, rfl, -⟩ := R.exists_of_arrowCount_ne_zero _ hj _ (R.st_lt p) (by omega)
    rw [R.arrowCount_st] at h
    obtain ⟨t, ht⟩ := Q.exists_arrowAt (p := p) (e := ⟨(q, p), ⟨k, h⟩⟩) (Or.inr rfl)
    have hqp : q ≠ p := by
      rintro rfl
      exact lt_irrefl q (Q.forward q q (by omega))
    refine ⟨t, ?_, ?_⟩
    · unfold slotJ otherEnd
      rw [ht]
      exact ite_eq_right hqp
    · unfold slotK
      rw [ht]

/-! ### The order of the factors -/

theorem slotRank_of_lt {i j : ℕ} (h : i < j) (hj : j < P.n) : P.slotRank i j = j - i - 1 := by
  unfold slotRank
  rw [show j + P.n - i - 1 = (j - i - 1) + P.n by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

theorem slotRank_of_gt {i j : ℕ} (h : j < i) (hi : i < P.n) :
    P.slotRank i j = j + P.n - i - 1 := by
  unfold slotRank
  rw [Nat.mod_eq_of_lt (by omega)]

/-- The rank of an arrow at `p` in the order of the slots, with its number. -/
def key (p : Fin Q.s) (e : Q.Arrow) : ℕ := P.slotRank (R.st p) (R.otherEnd p e) * 2 + e.2.1

theorem key_of_src {p : Fin Q.s} {e : Q.Arrow} (h : Q.src e = p) :
    R.key p e = (R.st (Q.tgt e) - R.st p - 1) * 2 + e.2.1 := by
  unfold key otherEnd
  rw [ite_eq_left h, slotRank_of_lt ((R.st_lt_st).mpr (lt_of_eq_of_lt h.symm (Q.src_lt_tgt e)))
    (R.st_lt _)]

theorem key_of_tgt {p : Fin Q.s} {e : Q.Arrow} (h : Q.tgt e = p) :
    R.key p e = (R.st (Q.src e) + P.n - R.st p - 1) * 2 + e.2.1 := by
  have hne : Q.src e ≠ p := fun h' => (Q.src_lt_tgt e).ne (h'.trans h.symm)
  unfold key otherEnd
  rw [ite_eq_right hne, slotRank_of_gt ((R.st_lt_st).mpr (lt_of_lt_of_eq (Q.src_lt_tgt e) h))
    (R.st_lt p)]

theorem key_out {p q : Fin Q.s} (hpq : p < q) (k : Fin (Q.arrows p q)) :
    R.key p ⟨(p, q), k⟩ = (R.st q - R.st p - 1) * 2 + k := by
  have h1 := (R.st_lt_st).mpr hpq
  have hs : Q.src (⟨(p, q), k⟩ : Q.Arrow) = p := rfl
  have ht : Q.tgt (⟨(p, q), k⟩ : Q.Arrow) = q := rfl
  unfold key otherEnd
  rw [ite_eq_left hs, ht, slotRank_of_lt h1 (R.st_lt q)]

theorem key_in {p q : Fin Q.s} (hpq : q < p) (k : Fin (Q.arrows q p)) :
    R.key p ⟨(q, p), k⟩ = (R.st q + P.n - R.st p - 1) * 2 + k := by
  have h1 := (R.st_lt_st).mpr hpq
  have hs : Q.src (⟨(q, p), k⟩ : Q.Arrow) = q := rfl
  unfold key otherEnd
  rw [ite_eq_right (show Q.src (⟨(q, p), k⟩ : Q.Arrow) ≠ p from hpq.ne), hs,
    slotRank_of_gt h1 (R.st_lt p)]

theorem pairwise_key (p : Fin Q.s) :
    (Q.vertexArrows p).Pairwise fun e e' => R.key p e < R.key p e' := by
  have hk2 : ∀ q q' (k : Fin (Q.arrows q q')), (k : ℕ) < 2 :=
    fun q q' k => lt_of_lt_of_le k.isLt (R.arrows_le_two q q')
  rw [ForwardQuiver.vertexArrows, List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [ForwardQuiver.outArrows, List.pairwise_flatMap]
    refine ⟨fun q _ => ?_, (List.pairwise_lt_finRange _).imp fun {q₁ q₂} hq => ?_⟩
    · rw [List.pairwise_map]
      refine (List.pairwise_lt_finRange _).imp fun {k k'} hk => ?_
      have hpq : p < q := Q.forward _ _ k.pos.ne'
      rw [R.key_out hpq, R.key_out hpq]
      exact Nat.add_lt_add_left hk _
    · intro x hx y hy
      simp only [List.mem_map, List.mem_finRange, true_and] at hx hy
      obtain ⟨k₁, rfl⟩ := hx
      obtain ⟨k₂, rfl⟩ := hy
      have hp1 : p < q₁ := Q.forward _ _ k₁.pos.ne'
      have hp2 : p < q₂ := Q.forward _ _ k₂.pos.ne'
      rw [R.key_out hp1, R.key_out hp2]
      have := (R.st_lt_st).mpr hq
      have := (R.st_lt_st).mpr hp1
      have := hk2 _ _ k₁
      omega
  · rw [ForwardQuiver.inArrows, List.pairwise_flatMap]
    refine ⟨fun q _ => ?_, (List.pairwise_lt_finRange _).imp fun {q₁ q₂} hq => ?_⟩
    · rw [List.pairwise_map]
      refine (List.pairwise_lt_finRange _).imp fun {k k'} hk => ?_
      have hqp : q < p := Q.forward _ _ k.pos.ne'
      rw [R.key_in hqp, R.key_in hqp]
      exact Nat.add_lt_add_left hk _
    · intro x hx y hy
      simp only [List.mem_map, List.mem_finRange, true_and] at hx hy
      obtain ⟨k₁, rfl⟩ := hx
      obtain ⟨k₂, rfl⟩ := hy
      have hp1 : q₁ < p := Q.forward _ _ k₁.pos.ne'
      have hp2 : q₂ < p := Q.forward _ _ k₂.pos.ne'
      rw [R.key_in hp1, R.key_in hp2]
      have := (R.st_lt_st).mpr hq
      have := (R.st_lt_st).mpr hp2
      have := hk2 _ _ k₁
      have := R.st_lt p
      omega
  · intro x hx y hy
    have hxs : Q.src x = p := (ForwardQuiver.mem_outArrows Q).mp hx
    have hyt : Q.tgt y = p := (ForwardQuiver.mem_inArrows Q).mp hy
    rw [R.key_of_src hxs, R.key_of_tgt hyt]
    have := (R.st_lt_st).mpr (lt_of_eq_of_lt hxs.symm (Q.src_lt_tgt x))
    have := (R.st_lt_st).mpr (lt_of_lt_of_eq (Q.src_lt_tgt y) hyt)
    have := hk2 _ _ x.2
    have := R.st_lt (Q.tgt x)
    omega

theorem key_arrowAt_lt_iff (p : Fin Q.s) (t t' : Fin (Q.valence p)) :
    R.key p (Q.arrowAt p t') < R.key p (Q.arrowAt p t) ↔ t' < t := by
  have hpw := List.pairwise_iff_getElem.mp (R.pairwise_key p)
  have hlen := Q.length_vertexArrows p
  constructor
  · intro h
    by_contra hle
    rcases (not_lt.mp hle).lt_or_eq with hlt | heq
    · have := hpw t.1 t'.1 (by omega) (by omega) hlt
      exact absurd h (not_lt.mpr this.le)
    · rw [heq] at h
      exact lt_irrefl _ h
  · intro h
    exact hpw t'.1 t.1 (by omega) (by omega) h

/-- **The order of the factors is the order of the slots.** -/
theorem lt_iff_slotBefore (p : Fin Q.s) (t t' : Fin (Q.valence p)) :
    t' < t ↔
      P.slotBefore (R.st p) (R.slotJ p t') (R.slotK p t') (R.slotJ p t) (R.slotK p t) = true := by
  rw [← R.key_arrowAt_lt_iff p t t']
  have hk := R.slotK_lt p t
  have hk' := R.slotK_lt p t'
  have hrank : ∀ u u' : Fin (Q.valence p),
      P.slotRank (R.st p) (R.slotJ p u) = P.slotRank (R.st p) (R.slotJ p u') →
        R.slotJ p u = R.slotJ p u' := by
    intro u u' h
    have hu := R.slotJ_lt p u
    have hu' := R.slotJ_lt p u'
    have hst := R.st_lt p
    rcases lt_or_gt_of_ne (show R.slotJ p u ≠ R.st p from fun h' => by
        by_cases hs : Q.src (Q.arrowAt p u) = p
        · exact (R.st_lt_slotJ hs).ne' h'
        · exact (R.slotJ_lt_st hs).ne h') with h1 | h1 <;>
      rcases lt_or_gt_of_ne (show R.slotJ p u' ≠ R.st p from fun h' => by
        by_cases hs : Q.src (Q.arrowAt p u') = p
        · exact (R.st_lt_slotJ hs).ne' h'
        · exact (R.slotJ_lt_st hs).ne h') with h2 | h2
    · rw [slotRank_of_gt h1 hst, slotRank_of_gt h2 hst] at h
      omega
    · rw [slotRank_of_gt h1 hst, slotRank_of_lt h2 hu'] at h
      omega
    · rw [slotRank_of_lt h1 hu, slotRank_of_gt h2 hst] at h
      omega
    · rw [slotRank_of_lt h1 hu, slotRank_of_lt h2 hu'] at h
      omega
  unfold key slotBefore
  change P.slotRank (R.st p) (R.slotJ p t') * 2 + R.slotK p t' <
      P.slotRank (R.st p) (R.slotJ p t) * 2 + R.slotK p t ↔ _
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · intro h
    rcases lt_trichotomy (P.slotRank (R.st p) (R.slotJ p t'))
      (P.slotRank (R.st p) (R.slotJ p t)) with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hrank _ _ h1, by omega⟩
    · omega
  · rintro (h | ⟨h1, h2⟩)
    · omega
    · rw [h1]
      omega

/-- **Sums over the slots** at `st p` are sums over the factors at `p`. -/
theorem sum_slots {M : Type*} [AddCommMonoid M] (p : Fin Q.s) (g : ℕ → ℕ → M)
    (hg : ∀ j < P.n, ∀ k < 2,
      (P.outSlot (R.st p) j k || P.inSlot (R.st p) j k) = false → g j k = 0) :
    ∑ j ∈ range P.n, ∑ k ∈ range 2, g j k = ∑ t, g (R.slotJ p t) (R.slotK p t) := by
  rw [← Finset.sum_product (f := fun x : ℕ × ℕ => g x.1 x.2)]
  have himg : (univ.image fun t => (R.slotJ p t, R.slotK p t)) ⊆ range P.n ×ˢ range 2 := by
    intro x hx
    simp only [mem_image, mem_univ, true_and] at hx
    obtain ⟨t, rfl⟩ := hx
    simp only [mem_product, mem_range]
    exact ⟨R.slotJ_lt p t, R.slotK_lt p t⟩
  rw [← Finset.sum_subset himg, Finset.sum_image]
  · intro t _ t' _ h
    simp only [Prod.mk.injEq] at h
    exact R.slot_injective p h.1 h.2
  · intro x hx hnot
    simp only [mem_product, mem_range] at hx
    apply hg x.1 hx.1 x.2 hx.2
    by_contra hb
    rw [Bool.not_eq_false] at hb
    obtain ⟨t, ht1, ht2⟩ := R.exists_slot p hx.1 hb
    exact hnot (mem_image.mpr ⟨t, mem_univ _, Prod.ext ht1 ht2⟩)

end Realizes

end PositionalQuiver

end Flat

end Schubert.RS.Quiver
