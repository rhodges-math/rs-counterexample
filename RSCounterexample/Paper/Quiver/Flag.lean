import RSCounterexample.Paper.Quiver.Schur.Dual

/-!
# The flag quiver

For a forward quiver `Q` with dimension vector `d`, the **flag quiver** `Q.flag` attaches to every
vertex `p` a chain of new vertices of dimensions `1, 2, …, d_p − 1`, pointing into `p`:
`(p, 0) → (p, 1) → ⋯ → (p, d_p − 2) → p`. The chain vertices are listed first, then the vertices
of `Q`, so `Q.flag` is again a forward quiver. A dominant weight `λ` of `∏_p GL(d_p)` gives a
weight `Q.flagWeight λ` of `Q.flag` that is constant on every vertex:
- `λ^{(p)}_k − λ^{(p)}_{k+1}` on the chain vertex `(p, k)`;
- the last entry `λ^{(p)}_{d_p − 1}` on the vertex `p`.

**Theorem** (`ForwardQuiver.multiplicity_flag`). For dominant `λ`,
`Q.flag.multiplicity (Q.flagWeight λ) = Q.multiplicity λ`.

So multiplicities of arbitrary irreducible modules in the coordinate ring of `Q` are
multiplicities of one-dimensional characters `∏_v det(g_v)^{σ_v}` for `Q.flag`.

Proof. Both sides count LR data (`ForwardQuiver.multiplicity_eq_card`). The arrows of `Q.flag`
are those of `Q` and one arrow out of every chain vertex (`ForwardQuiver.flagArrowEquiv`). At a
chain vertex `(p, k)` the factors are `s_{μ_k}` and `s_{μ_{k−1}}(x⁻¹)`, so by the rectangle rule
(`Schubert.RS.Quiver.Schur.weylProjector_ratSchur_mul_reverseNeg`) there is exactly one LR chain if
`μ_k = μ_{k−1} + (λ_k − λ_{k+1})` and none otherwise. This forces the chain shapes:
`μ_k = (λ_i − λ_{k+1})_{i ≤ k}` (`ForwardQuiver.chainShape`). At the vertex `p`, the last chain
factor `s_{μ_{d_p − 2}}(x⁻¹)` and the constant weight `λ_{d_p − 1}` give back the LR chains of
`Q` ending at `λ^{(p)}` (`Schubert.RS.Quiver.Schur.weylProjector_mul_reverseNeg`).

## Main definitions

* `ForwardQuiver.ChainVertex`, `ForwardQuiver.FlagVertex`, `ForwardQuiver.flagVertexEquiv`.
* `ForwardQuiver.flag`: the flag quiver.
* `ForwardQuiver.flagWeight`: the weight of the flag quiver attached to a weight of `Q`.
* `ForwardQuiver.flagArrowEquiv`: the arrows of `Q.flag` are those of `Q` and the chain arrows
  `ForwardQuiver.ChainArrow`.
* `ForwardQuiver.chainShape`, `ForwardQuiver.flagShapes`: the forced shapes on the chain arrows.

## Main results

* `ForwardQuiver.multiplicity_flag`: the flag identity.
* `ForwardQuiver.flagWeight_nsmul`: `flagWeight (N • λ) = N • flagWeight λ`.
-/

namespace Schubert.RS.Quiver.ForwardQuiver

open Schubert.RS.Quiver.Schur

variable (Q : ForwardQuiver)

/-! ## Vertices -/

/-- The length `d_p − 1` of the chain attached to the vertex `p`. -/
def chainLength (p : Fin Q.s) : ℕ := Q.dim p - 1

/-- The chain vertices `(p, k)` with `k < d_p − 1`; the vertex `(p, k)` has dimension `k + 1`. -/
abbrev ChainVertex : Type := (p : Fin Q.s) × Fin (Q.chainLength p)

/-- The vertices of the flag quiver: the chain vertices and the vertices of `Q`. -/
abbrev FlagVertex : Type := Q.ChainVertex ⊕ Fin Q.s

/-- The number of vertices of the flag quiver. -/
abbrev flagSize : ℕ := (∑ p, Q.chainLength p) + Q.s

/-- The numbering of the vertices of the flag quiver: first the chain vertices, chain by chain,
then the vertices of `Q`. -/
def vertexNumbering : Fin Q.flagSize ≃ Q.FlagVertex :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr finSigmaFinEquiv.symm (Equiv.refl _))

/-- The dimensions of the vertices of the flag quiver. -/
def flagDim : Q.FlagVertex → ℕ
  | .inl a => a.2 + 1
  | .inr p => Q.dim p

/-- The target of the arrow out of the chain vertex `(p, k)`: the next chain vertex `(p, k + 1)`,
or `p` itself at the end of the chain. -/
def chainTarget (a : Q.ChainVertex) : Q.FlagVertex :=
  if h : a.2.1 + 1 < Q.chainLength a.1 then .inl ⟨a.1, a.2.1 + 1, h⟩ else .inr a.1

/-- The number of arrows between two vertices of the flag quiver. -/
def flagArrows : Q.FlagVertex → Q.FlagVertex → ℕ
  | .inl a, w => if w = Q.chainTarget a then 1 else 0
  | .inr p, .inr q => Q.arrows p q
  | .inr _, .inl _ => 0

variable {Q}

theorem ChainVertex.ext {a b : Q.ChainVertex} (h₁ : a.1 = b.1) (h₂ : a.2.1 = b.2.1) : a = b := by
  obtain ⟨p, k⟩ := a
  obtain ⟨q, l⟩ := b
  dsimp only at h₁ h₂
  subst h₁
  exact congrArg _ (Fin.ext h₂)

theorem chainTarget_eq_inl_iff {a b : Q.ChainVertex} :
    Q.chainTarget b = .inl a ↔ b.1 = a.1 ∧ b.2.1 + 1 = a.2.1 := by
  obtain ⟨p, k, hk⟩ := a
  obtain ⟨q, l, hl⟩ := b
  simp only [chainTarget]
  split_ifs with h
  · constructor
    · intro he
      simp only [Sum.inl.injEq, Sigma.mk.injEq] at he
      obtain ⟨rfl, he⟩ := he
      exact ⟨rfl, congrArg Fin.val (eq_of_heq he)⟩
    · rintro ⟨rfl, he⟩
      simp only [Sum.inl.injEq]
      exact ChainVertex.ext rfl he
  · simp only [false_iff, not_and]
    rintro rfl he
    exact h (by simpa [he] using hk)

theorem chainTarget_eq_inr_iff {b : Q.ChainVertex} {p : Fin Q.s} :
    Q.chainTarget b = .inr p ↔ b.1 = p ∧ b.2.1 + 1 = Q.chainLength b.1 := by
  have hb := b.2.isLt
  simp only [chainTarget]
  split_ifs with h
  · simp only [false_iff, not_and]
    intro _ he
    omega
  · simp only [Sum.inr.injEq]
    constructor
    · intro he
      exact ⟨he, by omega⟩
    · exact fun he => he.1

theorem flagDim_chainTarget (a : Q.ChainVertex) : a.2.1 + 1 ≤ Q.flagDim (Q.chainTarget a) := by
  have ha := a.2.isLt
  simp only [chainTarget]
  split_ifs <;> simp only [flagDim, chainLength] at ha ⊢ <;> omega

theorem val_vertexNumbering_symm_inl (a : Q.ChainVertex) :
    (Q.vertexNumbering.symm (.inl a) : ℕ) = finSigmaFinEquiv a := by
  simp [vertexNumbering, Equiv.sumCongr_symm]

theorem val_vertexNumbering_symm_inr (p : Fin Q.s) :
    (Q.vertexNumbering.symm (.inr p) : ℕ) = (∑ p, Q.chainLength p) + p := by
  simp [vertexNumbering, Equiv.sumCongr_symm]

theorem vertexNumbering_symm_lt {x y : Q.FlagVertex} (h : Q.flagArrows x y ≠ 0) :
    Q.vertexNumbering.symm x < Q.vertexNumbering.symm y := by
  rw [Fin.lt_def]
  rcases x with a | p <;> rcases y with b | q
  · have hab : Q.chainTarget a = .inl b := by
      by_contra hne
      exact h (by simp [flagArrows, Ne.symm hne])
    obtain ⟨h₁, h₂⟩ := chainTarget_eq_inl_iff.mp hab
    obtain ⟨p, k⟩ := a
    obtain ⟨q, l⟩ := b
    dsimp only at h₁ h₂
    subst h₁
    rw [val_vertexNumbering_symm_inl, val_vertexNumbering_symm_inl, finSigmaFinEquiv_apply,
      finSigmaFinEquiv_apply]
    dsimp only at *
    omega
  · rw [val_vertexNumbering_symm_inl, val_vertexNumbering_symm_inr]
    exact lt_of_lt_of_le (finSigmaFinEquiv a).isLt (Nat.le_add_right _ _)
  · exact absurd rfl h
  · rw [val_vertexNumbering_symm_inr, val_vertexNumbering_symm_inr]
    have := Q.forward p q h
    rw [Fin.lt_def] at this
    omega

variable (Q)

/-! ## The flag quiver and its weight -/

/-- **The flag quiver** of `Q`: a chain `(p, 0) → (p, 1) → ⋯ → (p, d_p − 2) → p` of vertices of
dimensions `1, 2, …, d_p − 1` is attached to every vertex `p`. The chain vertices come first. -/
def flag : ForwardQuiver where
  s := Q.flagSize
  dim v := Q.flagDim (Q.vertexNumbering v)
  arrows u v := Q.flagArrows (Q.vertexNumbering u) (Q.vertexNumbering v)
  forward u v h := by simpa using vertexNumbering_symm_lt h

/-- The vertices of the flag quiver: the chain vertices and the vertices of `Q`. -/
def flagVertexEquiv : Fin Q.flag.s ≃ Q.FlagVertex := Q.vertexNumbering

theorem flag_dim_apply (v : Fin Q.flag.s) : Q.flag.dim v = Q.flagDim (Q.flagVertexEquiv v) :=
  rfl

@[simp]
theorem flag_dim_symm (w : Q.FlagVertex) :
    Q.flag.dim (Q.flagVertexEquiv.symm w) = Q.flagDim w := by
  rw [flag_dim_apply, Equiv.apply_symm_apply]

/-- The entries of `λ^{(p)}`, extended by `0`. -/
def weightEntry (lam : Q.Weight) (p : Fin Q.s) (i : ℕ) : ℤ :=
  if h : i < Q.dim p then lam p ⟨i, h⟩ else 0

/-- The value of the flag weight at a vertex of the flag quiver: `λ^{(p)}_k − λ^{(p)}_{k+1}` at
the chain vertex `(p, k)`, and `λ^{(p)}_{d_p − 1}` at `p`. -/
def flagConst (lam : Q.Weight) : Q.FlagVertex → ℤ
  | .inl a => Q.weightEntry lam a.1 a.2 - Q.weightEntry lam a.1 (a.2 + 1)
  | .inr p => Q.weightEntry lam p (Q.dim p - 1)

/-- **The flag weight**: the weight of the flag quiver attached to a weight `λ` of `Q`. It is
constant on every vertex: `λ^{(p)}_k − λ^{(p)}_{k+1}` on the chain vertex `(p, k)`, and the last
entry `λ^{(p)}_{d_p − 1}` on `p`. -/
def flagWeight (lam : Q.Weight) : Q.flag.Weight :=
  fun v _ => Q.flagConst lam (Q.flagVertexEquiv v)

theorem flagWeight_symm (lam : Q.Weight) (w : Q.FlagVertex) :
    Q.flagWeight lam (Q.flagVertexEquiv.symm w) = fun _ => Q.flagConst lam w := by
  funext i
  simp only [flagWeight, Equiv.apply_symm_apply]

theorem isDominant_flagWeight (lam : Q.Weight) : Q.flag.IsDominant (Q.flagWeight lam) :=
  fun _ _ _ _ => le_rfl

theorem weightEntry_nsmul (N : ℕ) (lam : Q.Weight) (p : Fin Q.s) (i : ℕ) :
    Q.weightEntry (N • lam) p i = N • Q.weightEntry lam p i := by
  simp only [weightEntry]
  split_ifs <;> simp

/-- **The flag weight is linear**: `flagWeight (N • λ) = N • flagWeight λ`. -/
theorem flagWeight_nsmul (N : ℕ) (lam : Q.Weight) :
    Q.flagWeight (N • lam) = N • Q.flagWeight lam := by
  funext v i
  simp only [flagWeight, Pi.smul_apply]
  rcases Q.flagVertexEquiv v with a | p
  · simp only [flagConst, weightEntry_nsmul, smul_sub]
  · simp only [flagConst, weightEntry_nsmul]

/-! ## Arrows -/

/-- The chain arrows: one arrow out of every chain vertex, to `Q.chainTarget`. -/
abbrev ChainArrow : Type := Q.ChainVertex

/-- The arrows of the flag quiver, in terms of its vertices. -/
def flagArrowSigmaEquiv :
    (Σ xy : Q.FlagVertex × Q.FlagVertex, Fin (Q.flagArrows xy.1 xy.2)) ≃
      Q.Arrow ⊕ Q.ChainArrow where
  toFun
    | ⟨(.inl a, _), _⟩ => .inr a
    | ⟨(.inr p, .inr q), k⟩ => .inl ⟨(p, q), k⟩
    | ⟨(.inr _, .inl _), k⟩ => k.elim0
  invFun
    | .inl e => ⟨(.inr e.1.1, .inr e.1.2), e.2⟩
    | .inr a => ⟨(.inl a, Q.chainTarget a), ⟨0, by simp [flagArrows]⟩⟩
  left_inv := by
    rintro ⟨⟨a | p, y⟩, k⟩
    · have hy : y = Q.chainTarget a := by
        by_contra h
        have := k.isLt
        simp [flagArrows, h] at this
      subst hy
      have hk : k = ⟨0, by simp [flagArrows]⟩ :=
        Fin.ext (by have := k.isLt; simp [flagArrows] at this; simp [this])
      subst hk
      rfl
    · rcases y with b | q
      · exact k.elim0
      · rfl
  right_inv := by
    rintro (e | a) <;> rfl

/-- **The arrows of the flag quiver** are the arrows of `Q` and one arrow out of every chain
vertex. -/
def flagArrowEquiv : Q.flag.Arrow ≃ Q.Arrow ⊕ Q.ChainArrow :=
  (Equiv.sigmaCongrLeft (β := fun xy : Q.FlagVertex × Q.FlagVertex =>
    Fin (Q.flagArrows xy.1 xy.2)) (Q.flagVertexEquiv.prodCongr Q.flagVertexEquiv)).trans
    Q.flagArrowSigmaEquiv

/-- The source of an arrow of the flag quiver. -/
def flagSrc : Q.Arrow ⊕ Q.ChainArrow → Q.FlagVertex
  | .inl e => .inr (Q.src e)
  | .inr a => .inl a

/-- The target of an arrow of the flag quiver. -/
def flagTgt : Q.Arrow ⊕ Q.ChainArrow → Q.FlagVertex
  | .inl e => .inr (Q.tgt e)
  | .inr a => Q.chainTarget a

@[simp]
theorem flag_src_symm (x : Q.Arrow ⊕ Q.ChainArrow) :
    Q.flag.src (Q.flagArrowEquiv.symm x) = Q.flagVertexEquiv.symm (Q.flagSrc x) := by
  rcases x with e | a <;> rfl

@[simp]
theorem flag_tgt_symm (x : Q.Arrow ⊕ Q.ChainArrow) :
    Q.flag.tgt (Q.flagArrowEquiv.symm x) = Q.flagVertexEquiv.symm (Q.flagTgt x) := by
  rcases x with e | a <;> rfl

/-- Products over the arrows of the flag quiver. -/
theorem prod_flagArrow {M : Type*} [CommMonoid M] (f : Q.flag.Arrow → M) :
    ∏ e, f e = (∏ e, f (Q.flagArrowEquiv.symm (.inl e))) *
      ∏ a, f (Q.flagArrowEquiv.symm (.inr a)) := by
  rw [← Fintype.prod_sum_type (fun x => f (Q.flagArrowEquiv.symm x))]
  exact (Equiv.prod_comp Q.flagArrowEquiv.symm f).symm

/-- The row bound of an arrow shape of the flag quiver, at the source. -/
theorem colLen_le_flagDim_src (μ' : Q.flag.ArrowShapes) (x : Q.Arrow ⊕ Q.ChainArrow) :
    (μ' (Q.flagArrowEquiv.symm x)).1.colLen 0 ≤ Q.flagDim (Q.flagSrc x) := by
  have h : ∀ ν : YoungDiagram, ν.colLen 0 ≤ min (Q.flag.dim (Q.flag.src (Q.flagArrowEquiv.symm x)))
      (Q.flag.dim (Q.flag.tgt (Q.flagArrowEquiv.symm x))) →
        ν.colLen 0 ≤ Q.flagDim (Q.flagSrc x) := by
    intro ν hν
    rw [flag_src_symm, flag_tgt_symm, flag_dim_symm] at hν
    exact hν.trans (min_le_left _ _)
  exact h _ (μ' _).2

/-- The row bound of an arrow shape of the flag quiver, at the target. -/
theorem colLen_le_flagDim_tgt (μ' : Q.flag.ArrowShapes) (x : Q.Arrow ⊕ Q.ChainArrow) :
    (μ' (Q.flagArrowEquiv.symm x)).1.colLen 0 ≤ Q.flagDim (Q.flagTgt x) := by
  have h : ∀ ν : YoungDiagram, ν.colLen 0 ≤ min (Q.flag.dim (Q.flag.src (Q.flagArrowEquiv.symm x)))
      (Q.flag.dim (Q.flag.tgt (Q.flagArrowEquiv.symm x))) →
        ν.colLen 0 ≤ Q.flagDim (Q.flagTgt x) := by
    intro ν hν
    rw [flag_src_symm, flag_tgt_symm, flag_dim_symm, flag_dim_symm] at hν
    exact hν.trans (min_le_right _ _)
  exact h _ (μ' _).2

/-! ## Chain shapes -/

/-- The shapes on the chain arrows of arrow shapes of the flag quiver. -/
def chainPart (μ' : Q.flag.ArrowShapes) (a : Q.ChainVertex) : YoungDiagram :=
  (μ' (Q.flagArrowEquiv.symm (.inr a))).1

theorem rowLen_bot_eq_zero (i : ℕ) : (⊥ : YoungDiagram).rowLen i = 0 := by
  by_contra h
  exact YoungDiagram.notMem_bot (i, 0) (YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero h))

theorem colLen_bot_eq_zero (j : ℕ) : (⊥ : YoungDiagram).colLen j = 0 := by
  by_contra h
  exact YoungDiagram.notMem_bot (0, j) (YoungDiagram.mem_iff_lt_colLen.mpr (Nat.pos_of_ne_zero h))

/-- The shape on the chain arrow into the chain vertex `a`, or `⊥` at the start of a chain. -/
def prevOf (f : Q.ChainVertex → YoungDiagram) : Q.ChainVertex → YoungDiagram
  | ⟨_, ⟨0, _⟩⟩ => ⊥
  | ⟨p, ⟨k + 1, hk⟩⟩ => f ⟨p, ⟨k, Nat.lt_of_succ_lt hk⟩⟩

variable {Q} in
theorem weightEntry_anti {lam : Q.Weight} (hlam : Q.IsDominant lam) (p : Fin Q.s) {i j : ℕ}
    (hij : i ≤ j) (hj : j < Q.dim p) : Q.weightEntry lam p j ≤ Q.weightEntry lam p i := by
  simp only [weightEntry, dite_eq_left hj, dite_eq_left (lt_of_le_of_lt hij hj)]
  exact hlam p (Fin.mk_le_mk.mpr hij)

theorem lt_dim_of_chainVertex (a : Q.ChainVertex) : a.2.1 + 1 < Q.dim a.1 := by
  have := a.2.isLt
  simp only [chainLength] at this
  omega

/-- The rows `λ^{(p)}_i − λ^{(p)}_{k+1}`, `i ≤ k`, of the forced shape out of the chain vertex
`(p, k)`. -/
def chainRows (lam : Q.Weight) (a : Q.ChainVertex) (i : Fin (a.2.1 + 1)) : ℕ :=
  (Q.weightEntry lam a.1 i - Q.weightEntry lam a.1 (a.2 + 1)).toNat

theorem antitone_chainRows {lam : Q.Weight} (hlam : Q.IsDominant lam) (a : Q.ChainVertex) :
    Antitone (Q.chainRows lam a) := fun i j hij => Int.toNat_le_toNat (by
  have := weightEntry_anti hlam a.1 (Fin.le_def.mp hij)
    (by have := Q.lt_dim_of_chainVertex a; omega)
  linarith)

/-- **The forced chain shapes**: on the arrow out of the chain vertex `(p, k)`, the Young diagram
with the `k + 1` rows `λ^{(p)}_i − λ^{(p)}_{k+1}`, `i ≤ k`. -/
def chainShape (lam : Q.Weight) (hlam : Q.IsDominant lam) (a : Q.ChainVertex) : YoungDiagram :=
  YoungDiagram.ofRowLensFin (Q.chainRows lam a) (Q.antitone_chainRows hlam a)

theorem colLen_chainShape_le {lam : Q.Weight} (hlam : Q.IsDominant lam) (a : Q.ChainVertex) :
    (Q.chainShape lam hlam a).colLen 0 ≤ a.2.1 + 1 :=
  YoungDiagram.colLen_zero_ofRowLensFin_le _ _

theorem rowLen_chainShape {lam : Q.Weight} (hlam : Q.IsDominant lam) (a : Q.ChainVertex)
    (i : ℕ) : ((Q.chainShape lam hlam a).rowLen i : ℤ) =
      if i ≤ a.2.1 then Q.weightEntry lam a.1 i - Q.weightEntry lam a.1 (a.2 + 1) else 0 := by
  split_ifs with hi
  · have h := YoungDiagram.rowLen_ofRowLensFin (Q.chainRows lam a) (Q.antitone_chainRows hlam a)
      ⟨i, Nat.lt_succ_of_le hi⟩
    simp only at h
    rw [chainShape, h, chainRows, Int.toNat_of_nonneg]
    have := weightEntry_anti hlam a.1 (Nat.le_succ_of_le hi) (Q.lt_dim_of_chainVertex a)
    linarith
  · rw [chainShape, YoungDiagram.rowLen_ofRowLensFin_eq_zero_of_le _ _ (by omega)]
    rfl

/-- The forced chain shapes grow by the flag weight: row `i ≤ k` of the shape out of `(p, k)` is
row `i` of the shape into `(p, k)` plus `λ^{(p)}_k − λ^{(p)}_{k+1}`. -/
theorem rowLen_chainShape_eq_prevOf {lam : Q.Weight} (hlam : Q.IsDominant lam)
    (a : Q.ChainVertex) {i : ℕ} (hi : i ≤ a.2.1) :
    ((Q.chainShape lam hlam a).rowLen i : ℤ) =
      (Q.prevOf (Q.chainShape lam hlam) a).rowLen i + Q.flagConst lam (.inl a) := by
  obtain ⟨p, k, hk⟩ := a
  rw [rowLen_chainShape, ite_eq_left hi]
  cases k with
  | zero =>
    simp only [prevOf, flagConst]
    have : i = 0 := by simpa using hi
    subst this
    simp [rowLen_bot_eq_zero]
  | succ k =>
    simp only [prevOf, flagConst]
    rw [rowLen_chainShape]
    rcases Nat.lt_or_ge i (k + 1) with h | h
    · rw [ite_eq_left (by simpa using Nat.le_of_lt_succ h)]
      simp only
      ring
    · have : i = k + 1 := by simp only at hi; omega
      subst this
      rw [ite_eq_right (by simp)]
      simp

/-- **The forced arrow shapes** of the flag quiver: those of `Q` on its arrows, the forced chain
shapes on the chain arrows. -/
def flagShapes {lam : Q.Weight} (hlam : Q.IsDominant lam) (μ : Q.ArrowShapes) :
    Q.flag.ArrowShapes := fun e' =>
  ⟨Sum.elim (fun e => (μ e).1) (Q.chainShape lam hlam) (Q.flagArrowEquiv e'), by
    have h₁ := Q.flagArrowEquiv.symm_apply_apply e'
    generalize Q.flagArrowEquiv e' = x at h₁ ⊢
    subst h₁
    rw [flag_src_symm, flag_tgt_symm, flag_dim_symm, flag_dim_symm]
    rcases x with e | a
    · exact (μ e).2
    · exact le_min (Q.colLen_chainShape_le hlam a)
        ((Q.colLen_chainShape_le hlam a).trans (Q.flagDim_chainTarget a))⟩

@[simp]
theorem flagShapes_symm_inl {lam : Q.Weight} (hlam : Q.IsDominant lam) (μ : Q.ArrowShapes)
    (e : Q.Arrow) : (Q.flagShapes hlam μ (Q.flagArrowEquiv.symm (.inl e))).1 = (μ e).1 := by
  simp [flagShapes]

@[simp]
theorem flagShapes_symm_inr {lam : Q.Weight} (hlam : Q.IsDominant lam) (μ : Q.ArrowShapes)
    (a : Q.ChainVertex) :
    (Q.flagShapes hlam μ (Q.flagArrowEquiv.symm (.inr a))).1 = Q.chainShape lam hlam a := by
  simp [flagShapes]

theorem chainPart_flagShapes {lam : Q.Weight} (hlam : Q.IsDominant lam) (μ : Q.ArrowShapes) :
    Q.chainPart (Q.flagShapes hlam μ) = Q.chainShape lam hlam := by
  funext a
  exact Q.flagShapes_symm_inr hlam μ a

theorem flagShapes_injective {lam : Q.Weight} (hlam : Q.IsDominant lam) :
    Function.Injective (Q.flagShapes hlam) := by
  intro μ₁ μ₂ h
  funext e
  apply Subtype.ext
  have := congrArg (fun μ' : Q.flag.ArrowShapes => (μ' (Q.flagArrowEquiv.symm (.inl e))).1) h
  simpa using this

/-! ## Counting at a vertex -/

/-- The number of LR chains at a vertex, as a Weyl projector of the product of the factors of the
outgoing and the incoming arrows. -/
theorem card_LRChain_vertexFactors (P : ForwardQuiver) (μ : P.ArrowShapes) (p : Fin P.s)
    {lam : Fin (P.dim p) → ℤ} (hlam : Antitone lam) :
    (Fintype.card (LRChain (P.vertexFactors μ p) lam) : ℤ) =
      weylProjector (lam ∘ ⇑(Fin.revPerm : Equiv.Perm (Fin (P.dim p))))
        ((∏ e, if P.src e = p then (outFactor (μ e).1).character (P.dim p) else 1) *
          ∏ e, if P.tgt e = p then (inFactor (P.dim p) (μ e).1).character (P.dim p) else 1) := by
  rw [← Finset.prod_filter, ← Finset.prod_filter, ← prod_vertexFactors_character]
  exact (weylProjector_prod_character (P.vertexFactors μ p) ⟨lam, hlam⟩).symm

theorem prod_chainTarget_inl {D : ℕ} (f : Q.ChainVertex → YoungDiagram) (a : Q.ChainVertex) :
    (∏ b, if Q.chainTarget b = .inl a then (inFactor D (f b)).character D else 1) =
      (inFactor D (Q.prevOf f a)).character D := by
  obtain ⟨p, k, hk⟩ := a
  cases k with
  | zero =>
    rw [Fintype.prod_eq_one]
    · rw [prevOf, character_inFactor D ⊥ (by simp [colLen_bot_eq_zero]),
        TauCeti.diagramSchurPoly_bot, map_one, map_one]
    · intro b
      rw [ite_eq_right]
      intro h
      have := (chainTarget_eq_inl_iff.mp h).2
      simp at this
  | succ k =>
    rw [Fintype.prod_eq_single ⟨p, ⟨k, Nat.lt_of_succ_lt hk⟩⟩]
    · have hT : Q.chainTarget ⟨p, ⟨k, Nat.lt_of_succ_lt hk⟩⟩ = .inl ⟨p, ⟨k + 1, hk⟩⟩ :=
        chainTarget_eq_inl_iff.mpr ⟨rfl, rfl⟩
      rw [ite_eq_left hT]
      rfl
    · intro b hb
      rw [ite_eq_right]
      intro h
      obtain ⟨h₁, h₂⟩ := chainTarget_eq_inl_iff.mp h
      exact hb (ChainVertex.ext h₁ (by simp only at h₂ ⊢; omega))

theorem prod_chainTarget_inr {M : Type*} [CommMonoid M] (g : Q.ChainVertex → M) (p : Fin Q.s) :
    (∏ b, if Q.chainTarget b = .inr p then g b else 1) =
      if h : 0 < Q.chainLength p then g ⟨p, ⟨Q.chainLength p - 1, by omega⟩⟩ else 1 := by
  split_ifs with hc
  · rw [Fintype.prod_eq_single ⟨p, ⟨Q.chainLength p - 1, by omega⟩⟩]
    · rw [ite_eq_left (chainTarget_eq_inr_iff.mpr ⟨rfl, by simp only; omega⟩)]
    · intro b hb
      rw [ite_eq_right]
      intro h
      obtain ⟨h₁, h₂⟩ := chainTarget_eq_inr_iff.mp h
      subst h₁
      exact hb (ChainVertex.ext rfl (by simp only; omega))
  · rw [Fintype.prod_eq_one]
    intro b
    rw [ite_eq_right]
    intro h
    obtain ⟨h₁, h₂⟩ := chainTarget_eq_inr_iff.mp h
    subst h₁
    have := b.2.isLt
    omega

theorem const_comp_revPerm {d : ℕ} (c : ℤ) :
    ((fun _ : Fin d => c) ∘ ⇑(Fin.revPerm : Equiv.Perm (Fin d))) = fun _ => c :=
  rfl

theorem colLen_chainPart_le (μ' : Q.flag.ArrowShapes) (a : Q.ChainVertex) :
    (Q.chainPart μ' a).colLen 0 ≤ a.2.1 + 1 :=
  Q.colLen_le_flagDim_src μ' (.inr a)

theorem colLen_prevOf_chainPart_le (μ' : Q.flag.ArrowShapes) (a : Q.ChainVertex) :
    (Q.prevOf (Q.chainPart μ') a).colLen 0 ≤ a.2.1 + 1 := by
  obtain ⟨p, k, hk⟩ := a
  cases k with
  | zero => simp [prevOf, colLen_bot_eq_zero]
  | succ k =>
    have h := Q.colLen_le_flagDim_tgt μ' (.inr ⟨p, ⟨k, Nat.lt_of_succ_lt hk⟩⟩)
    simp only [flagTgt] at h
    rw [show Q.chainTarget ⟨p, ⟨k, Nat.lt_of_succ_lt hk⟩⟩ = .inl ⟨p, ⟨k + 1, hk⟩⟩ from
      chainTarget_eq_inl_iff.mpr ⟨rfl, rfl⟩] at h
    exact h

/-- **The count at a chain vertex**: at the chain vertex `a = (p, k)` with the constant weight
`c`, there is exactly one LR chain if the shape out of `a` is the shape into `a` plus `c` in its
first `k + 1` rows, and none otherwise. -/
theorem card_flag_chainVertex (μ' : Q.flag.ArrowShapes) (a : Q.ChainVertex) (c : ℤ) :
    (Fintype.card (LRChain (Q.flag.vertexFactors μ' (Q.flagVertexEquiv.symm (.inl a)))
        fun _ : Fin (Q.flag.dim (Q.flagVertexEquiv.symm (.inl a))) => c) : ℤ) =
      if ∀ i ≤ a.2.1, ((Q.chainPart μ' a).rowLen i : ℤ) =
          (Q.prevOf (Q.chainPart μ') a).rowLen i + c then 1 else 0 := by
  rw [card_LRChain_vertexFactors Q.flag μ' _ antitone_const, Q.prod_flagArrow, Q.prod_flagArrow]
  simp only [flag_src_symm, flag_tgt_symm, flagSrc, flagTgt, EmbeddingLike.apply_eq_iff_eq,
    reduceCtorEq, ite_false, Finset.prod_const_one, one_mul, Sum.inl.injEq,
    Finset.prod_ite_eq', Finset.mem_univ, ite_true]
  rw [Q.prod_chainTarget_inl (fun b => (μ' (Q.flagArrowEquiv.symm (.inr b))).1) a,
    const_comp_revPerm]
  set D := Q.flag.dim (Q.flagVertexEquiv.symm (.inl a))
  have hD : D = a.2.1 + 1 := Q.flag_dim_symm _
  have hκ : (Q.chainPart μ' a).colLen 0 ≤ D := hD ▸ Q.colLen_chainPart_le μ' a
  have hν : (Q.prevOf (Q.chainPart μ') a).colLen 0 ≤ D := by
    rw [hD]
    exact Q.colLen_prevOf_chainPart_le μ' a
  change weylProjector (fun _ => c) ((outFactor (Q.chainPart μ' a)).character D *
    (inFactor D (Q.prevOf (Q.chainPart μ') a)).character D) = _
  rw [character_outFactor, toLaurent_diagramSchurPoly_eq_ratSchur _ hκ, character_inFactor D _ hν,
    weylProjector_ratSchur_mul_reverseNeg _ _ hν c]
  refine if_congr ?_ rfl rfl
  constructor
  · intro h i hi
    have := congrFun h ⟨i, by omega⟩
    simpa using this
  · intro h
    funext i
    have := h i (by have := i.isLt; omega)
    simpa using this

/-- **The chain shapes are forced**: if the flag quiver has LR data with the arrow shapes `μ'`
for the flag weight, then the shapes on the chain arrows are the forced chain shapes. -/
theorem chainPart_eq_chainShape {lam : Q.Weight} (hlam : Q.IsDominant lam)
    (μ' : Q.flag.ArrowShapes) (hne : Nonempty (Q.flag.VertexChains μ' (Q.flagWeight lam))) :
    Q.chainPart μ' = Q.chainShape lam hlam := by
  have hcond : ∀ b : Q.ChainVertex, ∀ i ≤ b.2.1, ((Q.chainPart μ' b).rowLen i : ℤ) =
      (Q.prevOf (Q.chainPart μ') b).rowLen i + Q.flagConst lam (.inl b) := by
    intro b
    have hpos : Fintype.card (LRChain (Q.flag.vertexFactors μ' (Q.flagVertexEquiv.symm (.inl b)))
        (Q.flagWeight lam (Q.flagVertexEquiv.symm (.inl b)))) ≠ 0 :=
      (Fintype.card_pos_iff.mpr ⟨hne.some _⟩).ne'
    rw [flagWeight_symm] at hpos
    have h := Q.card_flag_chainVertex μ' b (Q.flagConst lam (.inl b))
    split_ifs at h with hc
    · exact hc
    · exact absurd (by exact_mod_cast h) hpos
  have key : ∀ (p : Fin Q.s) (k : ℕ) (hk : k < Q.chainLength p),
      Q.chainPart μ' ⟨p, ⟨k, hk⟩⟩ = Q.chainShape lam hlam ⟨p, ⟨k, hk⟩⟩ := by
    intro p k
    induction k with
    | zero =>
      intro hk
      apply YoungDiagram.rowLen_injective
      funext i
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · have h₁ := hcond ⟨p, ⟨0, hk⟩⟩ 0 le_rfl
        have h₂ := Q.rowLen_chainShape_eq_prevOf hlam ⟨p, ⟨0, hk⟩⟩ (i := 0) le_rfl
        simp only [prevOf] at h₁ h₂
        exact_mod_cast h₁.trans h₂.symm
      · rw [YoungDiagram.rowLen_eq_zero_of_colLen_le ((Q.colLen_chainPart_le μ' _).trans hi),
          YoungDiagram.rowLen_eq_zero_of_colLen_le ((Q.colLen_chainShape_le hlam _).trans hi)]
    | succ k ih =>
      intro hk
      have hprev : Q.prevOf (Q.chainPart μ') ⟨p, ⟨k + 1, hk⟩⟩ =
          Q.prevOf (Q.chainShape lam hlam) ⟨p, ⟨k + 1, hk⟩⟩ := ih _
      apply YoungDiagram.rowLen_injective
      funext i
      rcases Nat.lt_or_ge (k + 1) i with hi | hi
      · rw [YoungDiagram.rowLen_eq_zero_of_colLen_le ((Q.colLen_chainPart_le μ' _).trans hi),
          YoungDiagram.rowLen_eq_zero_of_colLen_le ((Q.colLen_chainShape_le hlam _).trans hi)]
      · have h₁ := hcond ⟨p, ⟨k + 1, hk⟩⟩ i hi
        have h₂ := Q.rowLen_chainShape_eq_prevOf hlam ⟨p, ⟨k + 1, hk⟩⟩ hi
        rw [hprev] at h₁
        exact_mod_cast h₁.trans h₂.symm
  funext a
  exact key a.1 a.2.1 a.2.2

theorem mem_range_flagShapes {lam : Q.Weight} (hlam : Q.IsDominant lam) (μ' : Q.flag.ArrowShapes)
    (hne : Nonempty (Q.flag.VertexChains μ' (Q.flagWeight lam))) :
    μ' ∈ Set.range (Q.flagShapes hlam) := by
  have hμ : ∀ e : Q.Arrow, (μ' (Q.flagArrowEquiv.symm (.inl e))).1.colLen 0 ≤
      min (Q.dim (Q.src e)) (Q.dim (Q.tgt e)) := fun e =>
    le_min (Q.colLen_le_flagDim_src μ' (.inl e)) (Q.colLen_le_flagDim_tgt μ' (.inl e))
  refine ⟨fun e => ⟨(μ' (Q.flagArrowEquiv.symm (.inl e))).1, hμ e⟩, ?_⟩
  funext e'
  apply Subtype.ext
  obtain ⟨x, rfl⟩ := Q.flagArrowEquiv.symm.surjective e'
  rcases x with e | a
  · simp
  · rw [flagShapes_symm_inr, ← chainPart_eq_chainShape Q hlam μ' hne]
    rfl

/-- The count at a vertex `p` of `Q` in the flag quiver, after the vertex dimension is
identified with `d_p`. -/
theorem weylProjector_flag_vertex {lam : Q.Weight} (hlam : Q.IsDominant lam) (μ : Q.ArrowShapes)
    (p : Fin Q.s) (D : ℕ) (hD : D = Q.dim p) :
    weylProjector (fun _ : Fin D => Q.flagConst lam (.inr p))
        ((∏ e, if Q.src e = p then (outFactor (μ e).1).character D else 1) *
          ((∏ e, if Q.tgt e = p then (inFactor D (μ e).1).character D else 1) *
            if h : 0 < Q.chainLength p then (inFactor D
              (Q.chainShape lam hlam ⟨p, ⟨Q.chainLength p - 1, by omega⟩⟩)).character D
            else 1)) =
      weylProjector (lam p ∘ ⇑(Fin.revPerm : Equiv.Perm (Fin (Q.dim p))))
        ((∏ e, if Q.src e = p then (outFactor (μ e).1).character (Q.dim p) else 1) *
          ∏ e, if Q.tgt e = p then (inFactor (Q.dim p) (μ e).1).character (Q.dim p) else 1) := by
  subst hD
  have hG : IsSymmetric
      ((∏ e, if Q.src e = p then (outFactor (μ e).1).character (Q.dim p) else 1) *
        ∏ e, if Q.tgt e = p then (inFactor (Q.dim p) (μ e).1).character (Q.dim p) else 1) := by
    have h := prod_vertexFactors_character Q μ p
    rw [Finset.prod_filter, Finset.prod_filter] at h
    rw [← h]
    exact isSymmetric_prod_character _
  split_ifs with hc
  · set ν := Q.chainShape lam hlam ⟨p, ⟨Q.chainLength p - 1, by omega⟩⟩
    have hν : ν.colLen 0 ≤ Q.dim p := (Q.colLen_chainShape_le hlam _).trans (by
      simp only [chainLength] at hc ⊢
      omega)
    rw [← mul_assoc, character_inFactor _ ν hν, weylProjector_mul_reverseNeg hG ν hν]
    congr 2
    funext i
    have hi := i.isLt
    have e₁ : Q.chainLength p - 1 + 1 = Q.dim p - 1 := by
      simp only [chainLength] at hc ⊢
      omega
    have e₂ : Q.weightEntry lam p i = lam p i := by simp [weightEntry, hi]
    rw [TauCeti.DominantWeight.shift_apply, TauCeti.weightOfShape_apply, rowLen_chainShape]
    simp only [flagConst]
    split_ifs with h₁
    · rw [e₁, e₂]
      ring
    · have : (i : ℕ) = Q.dim p - 1 := by
        simp only [chainLength] at h₁ hc
        omega
      rw [← this, e₂]
      ring
  · rw [mul_one]
    congr 1
    funext i
    have hi := i.isLt
    simp only [chainLength, not_lt] at hc
    have hrev : (Fin.revPerm : Equiv.Perm (Fin (Q.dim p))) i = i :=
      Fin.ext (by simp only [Fin.revPerm_apply, Fin.val_rev]; omega)
    simp only [Function.comp_apply, hrev, flagConst, weightEntry]
    rw [dite_eq_left (by omega)]
    congr 1
    exact Fin.ext (by simp only; omega)

/-- **The count at a vertex of `Q`**: with the forced chain shapes, the LR chains of the flag
quiver at a vertex `p` of `Q` are as many as the LR chains of `Q` at `p`. -/
theorem card_flag_vertex {lam : Q.Weight} (hlam : Q.IsDominant lam) (μ : Q.ArrowShapes)
    (p : Fin Q.s) :
    Fintype.card (LRChain (Q.flag.vertexFactors (Q.flagShapes hlam μ)
        (Q.flagVertexEquiv.symm (.inr p)))
        fun _ : Fin (Q.flag.dim (Q.flagVertexEquiv.symm (.inr p))) => Q.flagConst lam (.inr p)) =
      Fintype.card (LRChain (Q.vertexFactors μ p) (lam p)) := by
  zify
  rw [card_LRChain_vertexFactors Q.flag _ _ antitone_const,
    card_LRChain_vertexFactors Q μ p (hlam p), Q.prod_flagArrow, Q.prod_flagArrow]
  simp only [flag_src_symm, flag_tgt_symm, flagSrc, flagTgt, EmbeddingLike.apply_eq_iff_eq,
    reduceCtorEq, ite_false, Finset.prod_const_one, mul_one, Sum.inr.injEq,
    flagShapes_symm_inl, flagShapes_symm_inr]
  rw [prod_chainTarget_inr, const_comp_revPerm]
  exact Q.weylProjector_flag_vertex hlam μ p _ (Q.flag_dim_symm (.inr p))

/-! ## The flag identity -/

/-- Two finite sigma types have the same cardinality if the fibres of the first are empty outside
the image of an injection, and have the cardinalities of the fibres of the second on it. -/
theorem natCard_sigma_eq_of_injective {α β : Type*} {X : α → Type*} {Y : β → Type*}
    [∀ a, Fintype (X a)] [∀ b, Fintype (Y b)] (Φ : β → α) (hΦ : Function.Injective Φ)
    (hX : ∀ a, Nonempty (X a) → a ∈ Set.range Φ)
    (hcard : ∀ b, Fintype.card (X (Φ b)) = Fintype.card (Y b)) :
    Nat.card (Σ a, X a) = Nat.card (Σ b, Y b) := by
  have e₁ : (Σ a, X a) ≃ Σ a : Set.range Φ, X a.1 :=
    (Equiv.subtypeUnivEquiv (p := fun x : Σ a, X a => x.1 ∈ Set.range Φ)
      fun x => hX x.1 ⟨x.2⟩).symm.trans (Equiv.subtypeSigmaEquiv X _)
  have e₂ : (Σ a : Set.range Φ, X a.1) ≃ Σ b, X (Φ b) :=
    (Equiv.sigmaCongrLeft (β := fun a : Set.range Φ => X a.1)
      (Equiv.ofInjective Φ hΦ)).symm
  have e₃ : (Σ b, X (Φ b)) ≃ Σ b, Y b :=
    Equiv.sigmaCongrRight fun b => Fintype.equivOfCardEq (hcard b)
  exact Nat.card_congr ((e₁.trans e₂).trans e₃)

theorem card_vertexChains_flagShapes {lam : Q.Weight} (hlam : Q.IsDominant lam)
    (μ : Q.ArrowShapes) :
    Fintype.card (Q.flag.VertexChains (Q.flagShapes hlam μ) (Q.flagWeight lam)) =
      Fintype.card (Q.VertexChains μ lam) := by
  rw [Fintype.card_pi, Fintype.card_pi,
    ← Equiv.prod_comp (Q.flagVertexEquiv.symm : Q.FlagVertex ≃ Fin Q.flag.s),
    Fintype.prod_sum_type]
  have hchain : ∀ a : Q.ChainVertex, Fintype.card (LRChain
      (Q.flag.vertexFactors (Q.flagShapes hlam μ) (Q.flagVertexEquiv.symm (.inl a)))
      (Q.flagWeight lam (Q.flagVertexEquiv.symm (.inl a)))) = 1 := by
    intro a
    rw [flagWeight_symm]
    have h := Q.card_flag_chainVertex (Q.flagShapes hlam μ) a (Q.flagConst lam (.inl a))
    rw [chainPart_flagShapes, ite_eq_left fun i hi => Q.rowLen_chainShape_eq_prevOf hlam a hi] at h
    exact_mod_cast h
  have hvert : ∀ p : Fin Q.s, Fintype.card (LRChain
      (Q.flag.vertexFactors (Q.flagShapes hlam μ) (Q.flagVertexEquiv.symm (.inr p)))
      (Q.flagWeight lam (Q.flagVertexEquiv.symm (.inr p)))) =
        Fintype.card (LRChain (Q.vertexFactors μ p) (lam p)) := by
    intro p
    rw [flagWeight_symm]
    exact Q.card_flag_vertex hlam μ p
  simp only [hchain, hvert, Finset.prod_const_one, one_mul]

/-- **The flag identity.** For a dominant weight `λ` of `∏_p GL(d_p)`, the multiplicity of
`⊗_p V_p^{λ^{(p)}}` in the coordinate ring of `Q` is the multiplicity of the one-dimensional
character with the constant weights `Q.flagWeight λ` in the coordinate ring of the flag
quiver. -/
theorem multiplicity_flag {lam : Q.Weight} (hlam : Q.IsDominant lam) :
    Q.flag.multiplicity (Q.flagWeight lam) = Q.multiplicity lam := by
  rw [Q.flag.multiplicity_eq_card (Q.isDominant_flagWeight lam), Q.multiplicity_eq_card hlam]
  congr 1
  exact natCard_sigma_eq_of_injective (Q.flagShapes hlam) (Q.flagShapes_injective hlam)
    (fun μ' hne => Q.mem_range_flagShapes hlam μ' hne)
    (fun μ => Q.card_vertexChains_flagShapes hlam μ)

end Schubert.RS.Quiver.ForwardQuiver
