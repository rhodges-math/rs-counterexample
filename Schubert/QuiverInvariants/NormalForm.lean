import Schubert.QuiverInvariants.HomParam

/-!
# Normal forms of homomorphisms and the cokernel step

Let `K` be an infinite field and `ι`, `κ` vertex families of a forward quiver. This file prepares
the induction that proves Schofield's bound on `ext` by passing from `W` to the cokernel of a
general homomorphism `V → W`.

* **Normal forms.** A homomorphism `φ : V → W` whose rank at each vertex `p` is `|ιI p|` becomes
  the standard homomorphism `[[0, 1], [0, 0]]` in suitable bases. In such bases the intertwining
  relation alone forces `V = [[B, y₁], [0, I]]` and `W = [[I, y₂], [0, C]]`, with the same block
  `I` (`FQuiver.exists_normalForm`).
* **Transitivity of general quotients.** If a general representation on `κ` has a
  subrepresentation of dimension `γ`, then every general quotient dimension of the representations
  on a family `ιC` of dimension `dim κ − γ` is a general quotient dimension on `κ`
  (`FQuiver.GeneralQuot.of_generalSub`). The proof fixes the change of coordinates that makes a
  representation block upper-triangular; every remaining condition is then polynomial in the
  blocks.
* **General rank.** The homomorphisms between the pairs of a nonempty principal open set are the
  values of a polynomial family; the generic ranks `γ p` of its members are attained
  simultaneously on a nonempty principal open set. A general representation on `ι` then has a
  quotient of dimension `γ` and a general representation on `κ` has a subrepresentation of
  dimension `γ`, and `γ ≠ 0` when `genericHom > 0`.
* **The cokernel step** (`FQuiver.exists_cokernelStep`): when `genericHom > 0` there is such a
  `γ ≠ 0`, and for every family `ιC` of dimension `dim κ − γ` there is a pair `(V, W)` whose
  `ext` is at most every `ext(V', C')` with `V'` on `ι` and `C'` on `ιC`.

## Main results

* `QuiverInvariants.exists_basis_sum_extend`: extending a linearly independent family to a basis
  indexed by a sum type.
* `QuiverInvariants.FQuiver.eq_blockRep_of_normalHom_mem_ker`, `FQuiver.exists_normalForm`.
* `QuiverInvariants.FQuiver.GeneralQuot.of_generalSub`.
* `QuiverInvariants.FQuiver.exists_cokernelStep`.
-/

open Matrix MvPolynomial Filter

namespace QuiverInvariants

noncomputable section

/-! ### Linear algebra -/

section LinearAlgebra

variable {K : Type*} [Field K]

/-- **Extending a linearly independent family** `v : α → E` to a basis of `E` indexed by
`α ⊕ β`, for any `β` of the complementary cardinality. -/
theorem exists_basis_sum_extend {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    {α β : Type*} [Fintype α] [Fintype β] (v : α → E) (hv : LinearIndependent K v)
    (h : Fintype.card α + Fintype.card β = Module.finrank K E) :
    ∃ b : Module.Basis (α ⊕ β) K E, ∀ i, b (Sum.inl i) = v i := by
  set S := Submodule.span K (Set.range v)
  obtain ⟨T, hT⟩ := S.exists_isCompl
  have hS : Module.finrank K S = Fintype.card α := finrank_span_eq_card hv
  have hTdim : Module.finrank K T = Fintype.card β := by
    have := Submodule.finrank_add_eq_of_isCompl hT
    omega
  let bS : Module.Basis α K S := Module.Basis.span hv
  let bT : Module.Basis β K T :=
    (Module.finBasisOfFinrankEq K T hTdim).reindex (Fintype.equivFin β).symm
  refine ⟨(bS.prod bT).map (Submodule.prodEquivOfIsCompl S T hT), fun i => ?_⟩
  simp only [Module.Basis.map_apply, Module.Basis.prod_apply, Sum.elim_inl, Function.comp_apply,
    LinearMap.inl_apply, Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, add_zero, bS]
  exact congrArg Subtype.val (Module.Basis.span_apply hv i)

/-- **Normal form of a linear map.** If `φ : K^m → K^n` has rank `|b|`, with `|a| + |b| = |m|`
and `|b| + |c| = |n|`, then there are bases of `K^m` indexed by `a ⊕ b` and of `K^n` indexed by
`b ⊕ c` in which `φ` kills the first block and maps the second block onto the first block. -/
theorem exists_bases_normalForm {m n a b c : Type*} [Fintype m] [Fintype n] [Fintype a]
    [Fintype b] [Fintype c] [DecidableEq m] (φ : Matrix n m K)
    (ha : Fintype.card a + Fintype.card b = Fintype.card m)
    (hb : Fintype.card b = Module.finrank K (LinearMap.range φ.mulVecLin))
    (hc : Fintype.card b + Fintype.card c = Fintype.card n) :
    ∃ (bV : Module.Basis (a ⊕ b) K (m → K)) (bW : Module.Basis (b ⊕ c) K (n → K)),
      (∀ k, φ *ᵥ bV (Sum.inl k) = 0) ∧ ∀ i, φ *ᵥ bV (Sum.inr i) = bW (Sum.inl i) := by
  classical
  have hrn := LinearMap.finrank_range_add_finrank_ker φ.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  obtain ⟨bV, hbVS, hbVrepr⟩ := FQuiver.exists_basis_sum_of_finrank
    (LinearMap.ker φ.mulVecLin) a b (by omega) (by rw [Module.finrank_fintype_fun_eq_card]; omega)
  have hind : LinearIndependent K fun i => φ *ᵥ bV (Sum.inr i) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have hmem : (∑ i, g i • bV (Sum.inr i)) ∈ LinearMap.ker φ.mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sum]
      simpa [Matrix.mulVec_smul] using hg
    have := hbVrepr _ hmem j
    simpa [map_sum, Finsupp.single_apply] using this
  obtain ⟨bW, hbW⟩ := exists_basis_sum_extend _ hind
    (by rw [Module.finrank_fintype_fun_eq_card]; exact hc)
  refine ⟨bV, bW, fun k => ?_, fun i => (hbW i).symm⟩
  have := hbVS k
  rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at this

end LinearAlgebra

namespace FQuiver

variable (Q : FQuiver)

/-! ### Normal forms of homomorphisms -/

section NormalForm

variable {K : Type*} [Field K] {ι κ : Fin Q.s → Type} [∀ p, Fintype (ι p)]
  [∀ p, DecidableEq (ι p)] [∀ p, Fintype (κ p)] [∀ p, DecidableEq (κ p)]

variable {Q}

/-- Changing coordinates on both sides maps homomorphisms to homomorphisms. -/
theorem vertexConj_mem_ker_ringel {ι' κ' : Fin Q.s → Type} [∀ p, Fintype (ι' p)]
    [∀ p, DecidableEq (ι' p)] [∀ p, Fintype (κ' p)] [∀ p, DecidableEq (κ' p)]
    {V : Q.Rep K ι} {W : Q.Rep K κ} {φ : VertexHom K ι κ}
    (hφ : φ ∈ LinearMap.ker (Q.ringel V W)) (P : VertexIso K ι ι') (P' : VertexIso K κ κ') :
    vertexConj P P' φ ∈ LinearMap.ker (Q.ringel (Q.transport P V) (Q.transport P' W)) := by
  rw [LinearMap.mem_ker, ringel_transport]
  simp [LinearMap.mem_ker.mp hφ]

variable {ιK ιI ιC : Fin Q.s → Type} [∀ p, Fintype (ιK p)] [∀ p, DecidableEq (ιK p)]
  [∀ p, Fintype (ιI p)] [∀ p, DecidableEq (ιI p)] [∀ p, Fintype (ιC p)]
  [∀ p, DecidableEq (ιC p)]

omit [∀ p, DecidableEq (ιK p)] [∀ p, DecidableEq (ιC p)] in
/-- **The intertwining relation forces the normal form.** If the standard homomorphism
`[[0, 1], [0, 0]]` is a homomorphism `V → W`, then `V = [[B, y₁], [0, I]]` and
`W = [[I, y₂], [0, C]]` with the same block `I`. -/
theorem eq_blockRep_of_normalHom_mem_ker {V : Q.Rep K (fun p => ιK p ⊕ ιI p)}
    {W : Q.Rep K (fun p => ιI p ⊕ ιC p)}
    (h : Q.normalHom K ιK ιI ιC ∈ LinearMap.ker (Q.ringel V W)) :
    V = Q.blockRep (fun e => (V e).toBlocks₁₁) (fun e => (V e).toBlocks₁₂)
        (fun e => (V e).toBlocks₂₂) ∧
      W = Q.blockRep (fun e => (V e).toBlocks₂₂) (fun e => (W e).toBlocks₁₂)
        (fun e => (W e).toBlocks₂₂) := by
  rw [mem_ker_ringel] at h
  have key : ∀ e r c, (W e * Q.normalHom K ιK ιI ιC (Q.src e)) r c =
      (Q.normalHom K ιK ιI ιC (Q.tgt e) * V e) r c := fun e r c => by rw [h e]
  have hWN : ∀ e r i, (W e * Q.normalHom K ιK ιI ιC (Q.src e)) r (Sum.inr i) =
      W e r (Sum.inl i) := fun e r i => by
    simp [normalHom, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  have hWN' : ∀ e r k, (W e * Q.normalHom K ιK ιI ιC (Q.src e)) r (Sum.inl k) = 0 :=
    fun e r k => by simp [normalHom, Matrix.mul_apply, Fintype.sum_sum_type]
  have hNV : ∀ e i c, (Q.normalHom K ιK ιI ιC (Q.tgt e) * V e) (Sum.inl i) c =
      V e (Sum.inr i) c := fun e i c => by
    simp [normalHom, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  have hNV' : ∀ e j c, (Q.normalHom K ιK ιI ιC (Q.tgt e) * V e) (Sum.inr j) c = 0 :=
    fun e j c => by simp [normalHom, Matrix.mul_apply, Fintype.sum_sum_type]
  constructor
  · funext e
    rw [blockRep_apply, ← Matrix.fromBlocks_toBlocks (V e)]
    congr 1
    ext i k
    have := key e (Sum.inl i) (Sum.inl k)
    rw [hWN', hNV] at this
    exact this.symm
  · funext e
    rw [blockRep_apply]
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (W e)]
    have h₁₁ : (W e).toBlocks₁₁ = (V e).toBlocks₂₂ := by
      ext i' i
      have := key e (Sum.inl i') (Sum.inr i)
      rwa [hWN, hNV] at this
    have h₂₁ : (W e).toBlocks₂₁ = 0 := by
      ext j i
      have := key e (Sum.inr j) (Sum.inr i)
      rwa [hWN, hNV'] at this
    rw [h₁₁, h₂₁]

/-- **Normal form of a homomorphism.** Let `φ : V → W` have rank `|ιI p|` at every vertex `p`,
with `|ιK p| + |ιI p| = |ι p|` and `|ιI p| + |ιC p| = |κ p|`. Then in suitable coordinates
`V = [[B, y₁], [0, I]]` on `ιK ⊕ ιI` and `W = [[I, y₂], [0, C]]` on `ιI ⊕ ιC`, and `φ` becomes
the standard homomorphism. -/
theorem exists_normalForm {V : Q.Rep K ι} {W : Q.Rep K κ} {φ : VertexHom K ι κ}
    (hφ : φ ∈ LinearMap.ker (Q.ringel V W))
    (hrank : ∀ p, Fintype.card (ιI p) = Module.finrank K (LinearMap.range (φ p).mulVecLin))
    (hK : ∀ p, Fintype.card (ιK p) + Fintype.card (ιI p) = Fintype.card (ι p))
    (hC : ∀ p, Fintype.card (ιI p) + Fintype.card (ιC p) = Fintype.card (κ p)) :
    ∃ (P : VertexIso K ι fun p => ιK p ⊕ ιI p) (P' : VertexIso K κ fun p => ιI p ⊕ ιC p),
      vertexConj P P' φ = Q.normalHom K ιK ιI ιC ∧
      ∃ (B : Q.Rep K ιK) (y₁ : Q.ArrowHom K ιI ιK) (I : Q.Rep K ιI) (y₂ : Q.ArrowHom K ιC ιI)
        (C : Q.Rep K ιC), Q.transport P V = Q.blockRep B y₁ I ∧
          Q.transport P' W = Q.blockRep I y₂ C := by
  have hb : ∀ p, ∃ (bV : Module.Basis (ιK p ⊕ ιI p) K (ι p → K))
      (bW : Module.Basis (ιI p ⊕ ιC p) K (κ p → K)),
      (∀ k, φ p *ᵥ bV (Sum.inl k) = 0) ∧ ∀ i, φ p *ᵥ bV (Sum.inr i) = bW (Sum.inl i) :=
    fun p => exists_bases_normalForm (φ p) (hK p) (hrank p) (hC p)
  choose bV bW hker himg using hb
  set P := VertexIso.ofBasis bV
  set P' := VertexIso.ofBasis bW
  have hconj : vertexConj P P' φ = Q.normalHom K ιK ιI ιC := by
    funext p
    ext r k
    rw [vertexConj_apply, Matrix.mul_assoc]
    have hcol : (fun j => (φ p * P.inv p) j k) = φ p *ᵥ bV p k := by
      funext j
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, P, VertexIso.ofBasis_inv_apply]
    have : (P'.hom p * (φ p * P.inv p)) r k = (P'.hom p *ᵥ (φ p *ᵥ bV p k)) r := by
      rw [← hcol]
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [this, VertexIso.ofBasis_hom_mulVec]
    rcases k with k | i
    · rw [hker, map_zero]
      rcases r with r | r <;> simp [normalHom]
    · rw [himg, Module.Basis.repr_self]
      rcases r with r | r <;> simp [normalHom, Finsupp.single_apply, Matrix.one_apply, eq_comm]
  refine ⟨P, P', hconj, ?_⟩
  have hN := vertexConj_mem_ker_ringel hφ P P'
  rw [hconj] at hN
  obtain ⟨hV, hW⟩ := eq_blockRep_of_normalHom_mem_ker hN
  exact ⟨_, _, _, _, _, hV, hW⟩

end NormalForm

/-! ### Block parts and polynomial maps -/

section BlockPart

variable {K : Type*} [Field K]

/-- A map between coordinate spaces each of whose coordinates is a coordinate or zero is
polynomial. -/
theorem isPolynomialMap_of_forall_eq_or {σ τ : Type*} (φ : (τ → K) → σ → K)
    (h : ∀ s, (∃ t, ∀ x, φ x s = x t) ∨ ∀ x, φ x s = 0) : IsPolynomialMap φ := fun s => by
  rcases h s with ⟨t, ht⟩ | h0
  · exact ⟨X t, fun x => by simp [ht]⟩
  · exact ⟨0, fun x => by simp [h0]⟩

variable {ι₁ ι₂ : Fin Q.s → Type}

/-- The block upper-triangular part `[[X₁₁, X₁₂], [0, X₂₂]]` of a representation on
`ι₁ ⊕ ι₂`. -/
def blockPart (X : Q.Rep K (fun p => ι₁ p ⊕ ι₂ p)) : Q.Rep K (fun p => ι₁ p ⊕ ι₂ p) :=
  Q.blockRep (fun e => (X e).toBlocks₁₁) (fun e => (X e).toBlocks₁₂) (fun e => (X e).toBlocks₂₂)

@[simp] theorem blockPart_blockRep (A : Q.Rep K ι₁) (y : Q.ArrowHom K ι₂ ι₁)
    (C : Q.Rep K ι₂) : Q.blockPart (Q.blockRep A y C) = Q.blockRep A y C := by
  funext e
  simp [blockPart]

/-- The second-block coordinates `⟨e, (i, k)⟩ ↦ ⟨e, (inr i, inr k)⟩`. -/
def inrEntry : Q.Entry ι₂ → Q.Entry (fun p => ι₁ p ⊕ ι₂ p) :=
  fun x => ⟨x.1, (Sum.inr x.2.1, Sum.inr x.2.2)⟩

theorem inrEntry_injective : Function.Injective (Q.inrEntry (ι₁ := ι₁) (ι₂ := ι₂)) := by
  rintro ⟨e, i, k⟩ ⟨e', i', k'⟩ h
  simp only [inrEntry, Sigma.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  simp only [heq_eq_eq, Prod.mk.injEq, Sum.inr.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

theorem toBlocks₂₂_ofCoord (x : Q.Entry (fun p => ι₁ p ⊕ ι₂ p) → K) :
    (fun e => (Q.ofCoord x e).toBlocks₂₂) = Q.ofCoord (x ∘ Q.inrEntry) :=
  rfl

theorem isPolynomialMap_coord_blockPart :
    IsPolynomialMap fun x : Q.Entry (fun p => ι₁ p ⊕ ι₂ p) → K =>
      Q.coord (Q.blockPart (Q.ofCoord x)) := by
  refine isPolynomialMap_of_forall_eq_or _ fun s => ?_
  obtain ⟨e, a, b⟩ := s
  rcases a with a | a <;> rcases b with b | b
  · exact Or.inl ⟨⟨e, Sum.inl a, Sum.inl b⟩, fun x => rfl⟩
  · exact Or.inr fun x => rfl
  · exact Or.inl ⟨⟨e, Sum.inr a, Sum.inl b⟩, fun x => rfl⟩
  · exact Or.inl ⟨⟨e, Sum.inr a, Sum.inr b⟩, fun x => rfl⟩

end BlockPart

/-! ### Transitivity of general quotients -/

section Transitivity

variable {K : Type*} [Field K] [Infinite K] {κ ιC : Fin Q.s → Type} [∀ p, Fintype (κ p)]
  [∀ p, DecidableEq (κ p)] [∀ p, Fintype (ιC p)] [∀ p, DecidableEq (ιC p)]

variable {Q}

/-- **Transitivity of general quotients.** Suppose a general representation on `κ` has a
subrepresentation of dimension `γ`, and let `ιC` be a family of dimension `dim κ − γ`. If a
general representation on `ιC` has a quotient of dimension `β`, so does a general representation
on `κ`. -/
theorem GeneralQuot.of_generalSub {γ β : Fin Q.s → ℕ} (hsub : Q.GeneralSub K κ γ)
    (hcard : ∀ p, γ p + Fintype.card (ιC p) = Fintype.card (κ p))
    (hquot : Q.GeneralQuot K ιC β) : Q.GeneralQuot K κ β := by
  intro f hf
  apply hsub f
  rintro _ ⟨W, ⟨S, hS, hdim⟩, rfl⟩
  obtain ⟨P, A, y, C, hP⟩ := hS.exists_transport_eq_blockRep Q (ι₁ := finFam γ) (ι₂ := ιC)
    (fun p => by simp [hdim]) (fun p => by simp [hcard])
  set L : (Q.Entry (fun p => Fin (γ p) ⊕ ιC p) → K) → Q.Entry κ → K :=
    fun x => Q.coordTransport P.symm (Q.coord (Q.blockPart (Q.ofCoord x))) with hLdef
  have hL : IsPolynomialMap L :=
    (Q.isPolynomialMap_coordTransport P.symm).comp Q.isPolynomialMap_coord_blockPart
  obtain ⟨g, hg⟩ := hL.exists_eval_comp f
  have hg0 : g = 0 := by
    apply hquot.preimage_comp (Q.inrEntry_injective (ι₁ := finFam γ)) g
    rintro z ⟨C', hC', hCz⟩
    rw [← hg]
    apply hf
    refine ⟨Q.transport P.symm (Q.blockPart (Q.ofCoord z)), ?_, rfl⟩
    refine HasQuotientOfDim.transport Q ?_ P.symm
    have hC'' : (fun e => (Q.ofCoord z e).toBlocks₂₂) = C' := by
      rw [toBlocks₂₂_ofCoord, ← hCz, ofCoord_coord]
    rw [blockPart, hC'']
    exact hC'.blockRep Q _ _
  have h0 := hg (Q.coord (Q.blockRep A y C))
  rw [hg0, map_zero] at h0
  have hx : L (Q.coord (Q.blockRep A y C)) = Q.coord W := by
    simp only [hLdef, ofCoord_coord, blockPart_blockRep, coordTransport_coord]
    rw [← hP, transport_symm_transport]
  rwa [hx] at h0

end Transitivity

/-! ### General rank -/

section GeneralRank

variable {K : Type*} [Field K] {ι κ : Fin Q.s → Type} [∀ p, Fintype (ι p)]
  [∀ p, DecidableEq (ι p)] [∀ p, Fintype (κ p)] [∀ p, DecidableEq (κ p)]

omit [∀ p, DecidableEq (ι p)] [∀ p, DecidableEq (κ p)] in
/-- A matrix of rank zero is zero. -/
theorem _root_.QuiverInvariants.eq_zero_of_rank_eq_zero {m n : Type*} [Fintype n]
    [DecidableEq n] {M : Matrix m n K} (h : M.rank = 0) : M = 0 := by
  have hr : LinearMap.range M.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h
  ext i j
  have : M *ᵥ Pi.single j 1 ∈ LinearMap.range M.mulVecLin := ⟨_, rfl⟩
  rw [hr, Submodule.mem_bot] at this
  simpa using congrFun this i

/-- The members of the polynomial family of homomorphisms built from a matrix `Pr`: at the vertex
`p`, the matrix of polynomials in the coordinates `(x, w)` of the pairs and of the vectors `w`
whose value is the block at `p` of `Pr(x) w`. -/
def homFamily (Pr : Matrix (VertexEntry ι κ) (VertexEntry ι κ)
      (MvPolynomial (Q.Entry ι ⊕ Q.Entry κ) K)) (p : Fin Q.s) :
    Matrix (κ p) (ι p) (MvPolynomial ((Q.Entry ι ⊕ Q.Entry κ) ⊕ VertexEntry ι κ) K) :=
  Matrix.of fun j i => ∑ y, rename Sum.inl (Pr ⟨p, (i, j)⟩ y) * X (Sum.inr y)

omit [∀ p, DecidableEq (ι p)] [∀ p, DecidableEq (κ p)] in
theorem homFamily_map_eval (Pr : Matrix (VertexEntry ι κ) (VertexEntry ι κ)
      (MvPolynomial (Q.Entry ι ⊕ Q.Entry κ) K)) (p : Fin Q.s)
    (x : (Q.Entry ι ⊕ Q.Entry κ) ⊕ VertexEntry ι κ → K) :
    (Q.homFamily Pr p).map (eval x) =
      (vertexCoord K ι κ).symm (Pr.map (eval (x ∘ Sum.inl)) *ᵥ (x ∘ Sum.inr)) p := by
  ext j i
  simp [homFamily, Matrix.mulVec, dotProduct, eval_rename]

variable {Q}

/-- **The general rank of homomorphisms.** There is a dimension vector `γ` such that:
* a general representation on `ι` has a quotient of dimension `γ`, and a general representation on
  `κ` has a subrepresentation of dimension `γ`;
* some hom-generic pair has a homomorphism of rank `γ p` at every vertex `p`;
* `γ ≠ 0` when `genericHom > 0`.

It is the vector of generic ranks of a polynomial family of homomorphisms; these generic ranks are
attained simultaneously on a nonempty principal open set. -/
theorem exists_generalRank [Infinite K] :
    ∃ γ : Fin Q.s → ℕ, (∀ p, γ p ≤ Fintype.card (ι p)) ∧ (∀ p, γ p ≤ Fintype.card (κ p)) ∧
      (0 < Q.genericHom K ι κ → ∃ p, 0 < γ p) ∧ Q.GeneralQuot K ι γ ∧ Q.GeneralSub K κ γ ∧
      ∃ (V : Q.Rep K ι) (W : Q.Rep K κ) (φ : VertexHom K ι κ), Q.IsHomGeneric V W ∧
        φ ∈ LinearMap.ker (Q.ringel V W) ∧
        ∀ p, Module.finrank K (LinearMap.range (φ p).mulVecLin) = γ p := by
  obtain ⟨D, Pr, hD, hPr⟩ := Q.exists_homProjector (K := K) (ι := ι) (κ := κ)
  set γ : Fin Q.s → ℕ := fun p => genericRank (Q.homFamily Pr p) with hγ
  set G : ((Q.Entry ι ⊕ Q.Entry κ) ⊕ VertexEntry ι κ → K) → Prop := fun x =>
    eval (x ∘ Sum.inl) D ≠ 0 ∧ ∀ p, ((Q.homFamily Pr p).map (eval x)).rank = γ p with hGdef
  have hG : ∀ᶠ x in genericFilter K ((Q.Entry ι ⊕ Q.Entry κ) ⊕ VertexEntry ι κ), G x := by
    have hD' : rename (Sum.inl : Q.Entry ι ⊕ Q.Entry κ → _ ⊕ VertexEntry ι κ) D ≠ 0 := by
      rw [Ne, ← map_zero (rename (Sum.inl : Q.Entry ι ⊕ Q.Entry κ → _ ⊕ VertexEntry ι κ))]
      exact fun h => hD (rename_injective _ Sum.inl_injective h)
    filter_upwards [eventually_eval_ne_zero hD',
      Filter.eventually_all.mpr fun p => eventually_rank_eq_genericRank (Q.homFamily Pr p)]
      with x hx₁ hx₂
    exact ⟨by rwa [eval_rename] at hx₁, hx₂⟩
  -- the homomorphism at a good point
  have hpt : ∀ x, G x → Q.IsHomGeneric (Q.pairFst (x ∘ Sum.inl)) (Q.pairSnd (x ∘ Sum.inl)) ∧
      (vertexCoord K ι κ).symm (Pr.map (eval (x ∘ Sum.inl)) *ᵥ (x ∘ Sum.inr)) ∈
        LinearMap.ker (Q.ringel (Q.pairFst (x ∘ Sum.inl)) (Q.pairSnd (x ∘ Sum.inl))) ∧
      ∀ p, Module.finrank K (LinearMap.range ((vertexCoord K ι κ).symm
        (Pr.map (eval (x ∘ Sum.inl)) *ᵥ (x ∘ Sum.inr)) p).mulVecLin) = γ p := by
    intro x hx
    obtain ⟨hgen, hhom, -⟩ := hPr _ hx.1
    refine ⟨hgen, hhom _, fun p => ?_⟩
    rw [← homFamily_map_eval]
    exact hx.2 p
  obtain ⟨x₀, hx₀⟩ := hG.exists
  obtain ⟨hgen₀, hhom₀, hrank₀⟩ := hpt x₀ hx₀
  have hbound : ∀ p, γ p ≤ Fintype.card (ι p) ∧ γ p ≤ Fintype.card (κ p) := fun p => by
    set M := (vertexCoord K ι κ).symm (Pr.map (eval (x₀ ∘ Sum.inl)) *ᵥ (x₀ ∘ Sum.inr)) p
    have h₁ : M.rank ≤ Fintype.card (ι p) := M.rank_le_card_width
    have h₂ : M.rank ≤ Fintype.card (κ p) := M.rank_le_card_height
    rw [← hrank₀ p]
    exact ⟨h₁, h₂⟩
  have hdense := zariskiDense_of_eventually hG
  refine ⟨γ, fun p => (hbound p).1, fun p => (hbound p).2, fun hpos => ?_, ?_, ?_,
    ⟨_, _, _, hgen₀, hhom₀, hrank₀⟩⟩
  · -- `γ ≠ 0`
    by_contra hall
    push Not at hall
    have hhom := (Q.isHomGeneric_iff_homDim.mp hgen₀).symm ▸ hpos
    obtain ⟨ψ, hψ, hψ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (p := LinearMap.ker (Q.ringel (Q.pairFst (x₀ ∘ Sum.inl)) (Q.pairSnd (x₀ ∘ Sum.inl))))
      fun h => by
      rw [homDim, h, finrank_bot] at hhom
      exact lt_irrefl 0 hhom
    obtain ⟨-, -, hmul⟩ := hPr _ hx₀.1
    set x' : (Q.Entry ι ⊕ Q.Entry κ) ⊕ VertexEntry ι κ → K :=
      Sum.elim (x₀ ∘ Sum.inl) (vertexCoord K ι κ ψ)
    have hzero : (vertexCoord K ι κ).symm
        (Pr.map (eval (x₀ ∘ Sum.inl)) *ᵥ vertexCoord K ι κ ψ) = 0 := by
      funext p
      have h0 : ((Q.homFamily Pr p).map (eval x')).rank = 0 :=
        Nat.eq_zero_of_le_zero ((rank_map_eval_le_genericRank _ _).trans (hall p))
      have := eq_zero_of_rank_eq_zero h0
      rw [homFamily_map_eval] at this
      exact this
    rw [hmul ψ hψ, LinearEquiv.map_eq_zero_iff, smul_eq_zero] at hzero
    rcases hzero with h | h
    · exact hx₀.1 h
    · exact hψ0 ((vertexCoord K ι κ).map_eq_zero_iff.mp h)
  · -- a general representation on `ι` has a quotient of dimension `γ`
    have hπ : ZariskiDense (Set.range fun x : (Q.Entry ι ⊕ Q.Entry κ) ⊕ VertexEntry ι κ → K =>
        x ∘ (Sum.inl ∘ Sum.inl)) :=
      zariskiDense_univ.mono fun y _ => ⟨Sum.elim (Sum.elim y 0) 0, rfl⟩
    refine (ZariskiDense.image (isPolynomialMap_comp_right _) hπ hdense).mono ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨-, hhom, hrank⟩ := hpt x hx
    refine ⟨Q.pairFst (x ∘ Sum.inl), ⟨_, Q.isSubrep_ker hhom, fun p => ?_⟩, rfl⟩
    have := LinearMap.finrank_range_add_finrank_ker
      (((vertexCoord K ι κ).symm (Pr.map (eval (x ∘ Sum.inl)) *ᵥ (x ∘ Sum.inr))) p).mulVecLin
    rw [hrank p, Module.finrank_fintype_fun_eq_card] at this
    omega
  · -- a general representation on `κ` has a subrepresentation of dimension `γ`
    have hπ : ZariskiDense (Set.range fun x : (Q.Entry ι ⊕ Q.Entry κ) ⊕ VertexEntry ι κ → K =>
        x ∘ (Sum.inl ∘ Sum.inr)) :=
      zariskiDense_univ.mono fun y _ => ⟨Sum.elim (Sum.elim 0 y) 0, rfl⟩
    refine (ZariskiDense.image (isPolynomialMap_comp_right _) hπ hdense).mono ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨-, hhom, hrank⟩ := hpt x hx
    exact ⟨Q.pairSnd (x ∘ Sum.inl), ⟨_, Q.isSubrep_range hhom, hrank⟩, rfl⟩

omit [∀ p, DecidableEq (ι p)] [∀ p, DecidableEq (κ p)] in
/-- A pair at which some maximal minor of the generic Ringel matrix does not vanish is
hom-generic. -/
theorem isHomGeneric_of_eval_det_ne_zero [∀ p, DecidableEq (ι p)] [∀ p, DecidableEq (κ p)]
    {f : Fin (Q.genericRingelRank K ι κ) → Q.ArrowEntry ι κ}
    {g : Fin (Q.genericRingelRank K ι κ) → VertexEntry ι κ} {x : Q.Entry ι ⊕ Q.Entry κ → K}
    (h : eval x ((Q.genericRingelMatrix K ι κ).submatrix f g).det ≠ 0) :
    Q.IsHomGeneric (Q.pairFst x) (Q.pairSnd x) := by
  rw [IsHomGeneric, ringelRank_eq_rank_map_eval]
  refine le_antisymm (rank_map_eval_le_genericRank _ _) ?_
  exact le_rank_iff_exists_det_submatrix_ne_zero.mpr ⟨f, g, by rwa [← eval_det_submatrix]⟩

end GeneralRank

/-! ### The cokernel step -/

section CokernelStep

variable {K : Type*} [Field K] {ιK ιI ιC : Fin Q.s → Type}

/-- The normal-form pair of a pair `(V, W)` on `ιK ⊕ ιI` and `ιI ⊕ ιC`: the block upper-triangular
part `[[B, y₁], [0, I]]` of `V`, and `[[I, y₂], [0, C]]` with the blocks `y₂`, `C` of `W`. -/
def normalPair (x : Q.Entry (fun p => ιK p ⊕ ιI p) ⊕ Q.Entry (fun p => ιI p ⊕ ιC p) → K) :
    Q.Entry (fun p => ιK p ⊕ ιI p) ⊕ Q.Entry (fun p => ιI p ⊕ ιC p) → K :=
  Q.pairCoord (Q.blockPart (Q.pairFst x))
    (Q.blockRep (fun e => (Q.pairFst x e).toBlocks₂₂) (fun e => (Q.pairSnd x e).toBlocks₁₂)
      (fun e => (Q.pairSnd x e).toBlocks₂₂))

/-- The pair formed by the first member of the normal-form pair and the quotient block `C`. -/
def normalQuotPair (x : Q.Entry (fun p => ιK p ⊕ ιI p) ⊕ Q.Entry (fun p => ιI p ⊕ ιC p) → K) :
    Q.Entry (fun p => ιK p ⊕ ιI p) ⊕ Q.Entry ιC → K :=
  Q.pairCoord (Q.blockPart (Q.pairFst x)) (fun e => (Q.pairSnd x e).toBlocks₂₂)

theorem isPolynomialMap_normalPair :
    IsPolynomialMap (Q.normalPair (K := K) (ιK := ιK) (ιI := ιI) (ιC := ιC)) := by
  refine isPolynomialMap_of_forall_eq_or _ fun s => ?_
  rcases s with ⟨e, a, b⟩ | ⟨e, a, b⟩ <;> rcases a with a | a <;> rcases b with b | b
  · exact Or.inl ⟨Sum.inl ⟨e, Sum.inl a, Sum.inl b⟩, fun x => rfl⟩
  · exact Or.inr fun x => rfl
  · exact Or.inl ⟨Sum.inl ⟨e, Sum.inr a, Sum.inl b⟩, fun x => rfl⟩
  · exact Or.inl ⟨Sum.inl ⟨e, Sum.inr a, Sum.inr b⟩, fun x => rfl⟩
  · exact Or.inl ⟨Sum.inl ⟨e, Sum.inr a, Sum.inr b⟩, fun x => rfl⟩
  · exact Or.inr fun x => rfl
  · exact Or.inl ⟨Sum.inr ⟨e, Sum.inr a, Sum.inl b⟩, fun x => rfl⟩
  · exact Or.inl ⟨Sum.inr ⟨e, Sum.inr a, Sum.inr b⟩, fun x => rfl⟩

theorem isPolynomialMap_normalQuotPair :
    IsPolynomialMap (Q.normalQuotPair (K := K) (ιK := ιK) (ιI := ιI) (ιC := ιC)) := by
  refine isPolynomialMap_of_forall_eq_or _ fun s => ?_
  rcases s with ⟨e, a, b⟩ | ⟨e, a, b⟩
  · rcases a with a | a <;> rcases b with b | b
    · exact Or.inl ⟨Sum.inl ⟨e, Sum.inl a, Sum.inl b⟩, fun x => rfl⟩
    · exact Or.inr fun x => rfl
    · exact Or.inl ⟨Sum.inl ⟨e, Sum.inr a, Sum.inl b⟩, fun x => rfl⟩
    · exact Or.inl ⟨Sum.inl ⟨e, Sum.inr a, Sum.inr b⟩, fun x => rfl⟩
  · exact Or.inl ⟨Sum.inr ⟨e, Sum.inr a, Sum.inr b⟩, fun x => rfl⟩

theorem normalPair_pairCoord (B : Q.Rep K ιK) (y₁ : Q.ArrowHom K ιI ιK) (I : Q.Rep K ιI)
    (y₂ : Q.ArrowHom K ιC ιI) (C : Q.Rep K ιC) :
    Q.normalPair (Q.pairCoord (Q.blockRep B y₁ I) (Q.blockRep I y₂ C)) =
      Q.pairCoord (Q.blockRep B y₁ I) (Q.blockRep I y₂ C) := by
  simp [normalPair, blockRep_apply]

theorem normalQuotPair_pairCoord (B : Q.Rep K ιK) (y₁ : Q.ArrowHom K ιI ιK) (I : Q.Rep K ιI)
    (y₂ : Q.ArrowHom K ιC ιI) (C : Q.Rep K ιC) :
    Q.normalQuotPair (Q.pairCoord (Q.blockRep B y₁ I) (Q.blockRep I y₂ C)) =
      Q.pairCoord (Q.blockRep B y₁ I) C := by
  simp [normalQuotPair, blockRep_apply]

variable [∀ p, Fintype (ιK p)] [∀ p, DecidableEq (ιK p)] [∀ p, Fintype (ιI p)]
  [∀ p, DecidableEq (ιI p)] [∀ p, Fintype (ιC p)] [∀ p, DecidableEq (ιC p)] [Infinite K]

variable {Q}

/-- **A good normal-form pair.** Suppose some hom-generic pair is in the normal form
`([[B, y₁], [0, I]], [[I, y₂], [0, C]])`, and some pair `([[B, y₁], [0, I]], C)` is hom-generic.
Then there is a single normal-form pair at which both are hom-generic. -/
theorem exists_normalForm_isHomGeneric_both {B₁ : Q.Rep K ιK} {y₁ : Q.ArrowHom K ιI ιK}
    {I₁ : Q.Rep K ιI} {y₂ : Q.ArrowHom K ιC ιI} {C₁ : Q.Rep K ιC}
    (h₁ : Q.IsHomGeneric (Q.blockRep B₁ y₁ I₁) (Q.blockRep I₁ y₂ C₁)) {B₂ : Q.Rep K ιK}
    {y₁' : Q.ArrowHom K ιI ιK} {I₂ : Q.Rep K ιI} {C₂ : Q.Rep K ιC}
    (h₂ : Q.IsHomGeneric (Q.blockRep B₂ y₁' I₂) C₂) :
    ∃ (B : Q.Rep K ιK) (y : Q.ArrowHom K ιI ιK) (I : Q.Rep K ιI) (y' : Q.ArrowHom K ιC ιI)
      (C : Q.Rep K ιC), Q.IsHomGeneric (Q.blockRep B y I) (Q.blockRep I y' C) ∧
        Q.IsHomGeneric (Q.blockRep B y I) C := by
  obtain ⟨f₁, g₁, hfg₁⟩ := h₁.exists_minor
  obtain ⟨f₂, g₂, hfg₂⟩ := h₂.exists_minor
  obtain ⟨F₁, hF₁⟩ := (Q.isPolynomialMap_normalPair (K := K) (ιK := ιK) (ιI := ιI)
    (ιC := ιC)).exists_eval_comp
      ((Q.genericRingelMatrix K (fun p => ιK p ⊕ ιI p) (fun p => ιI p ⊕ ιC p)).submatrix
        f₁ g₁).det
  obtain ⟨F₂, hF₂⟩ := (Q.isPolynomialMap_normalQuotPair (K := K) (ιK := ιK) (ιI := ιI)
    (ιC := ιC)).exists_eval_comp
      ((Q.genericRingelMatrix K (fun p => ιK p ⊕ ιI p) ιC).submatrix f₂ g₂).det
  have hF₁0 : F₁ ≠ 0 := by
    rintro rfl
    have := hF₁ (Q.pairCoord (Q.blockRep B₁ y₁ I₁) (Q.blockRep I₁ y₂ C₁))
    rw [normalPair_pairCoord, map_zero] at this
    exact hfg₁ this
  have hF₂0 : F₂ ≠ 0 := by
    rintro rfl
    have := hF₂ (Q.pairCoord (Q.blockRep B₂ y₁' I₂) (Q.blockRep I₂ 0 C₂))
    rw [normalQuotPair_pairCoord, map_zero] at this
    exact hfg₂ this
  obtain ⟨x, -, hx⟩ := zariskiDense_univ.exists_eval_ne_zero (mul_ne_zero hF₁0 hF₂0)
  rw [map_mul] at hx
  have hx₁ := left_ne_zero_of_mul hx
  have hx₂ := right_ne_zero_of_mul hx
  rw [← hF₁] at hx₁
  rw [← hF₂] at hx₂
  refine ⟨fun e => (Q.pairFst x e).toBlocks₁₁, fun e => (Q.pairFst x e).toBlocks₁₂,
    fun e => (Q.pairFst x e).toBlocks₂₂, fun e => (Q.pairSnd x e).toBlocks₁₂,
    fun e => (Q.pairSnd x e).toBlocks₂₂, ?_, ?_⟩
  · have := isHomGeneric_of_eval_det_ne_zero hx₁
    rwa [normalPair, pairFst_pairCoord, pairSnd_pairCoord, blockPart] at this
  · have := isHomGeneric_of_eval_det_ne_zero hx₂
    rwa [normalQuotPair, pairFst_pairCoord, pairSnd_pairCoord, blockPart] at this

end CokernelStep

section Cokernel

variable {K : Type*} [Field K] [Infinite K] {ι κ : Fin Q.s → Type} [∀ p, Fintype (ι p)]
  [∀ p, DecidableEq (ι p)] [∀ p, Fintype (κ p)] [∀ p, DecidableEq (κ p)]

variable {Q}

/-- **The cokernel step.** If `genericHom > 0`, there is a dimension vector `γ ≠ 0`, `γ ≤ dim κ`,
such that for every family `ιC` of dimension `dim κ − γ`:
* every general quotient dimension on `ιC` is a general quotient dimension on `κ`;
* some pair `(V, W)` on `(ι, κ)` has `ext(V, W) ≤ ext(V', C')` for all `V'` on `ι` and `C'` on
  `ιC`.

The pair is a hom-generic pair in normal form `([[B, y₁], [0, I]], [[I, y₂], [0, C]])` such that
`([[B, y₁], [0, I]], C)` is hom-generic as well; by the quotient lemma
`ext(V, W) = ext(V, C)`. -/
theorem exists_cokernelStep (hpos : 0 < Q.genericHom K ι κ) :
    ∃ γ : Fin Q.s → ℕ, (∃ p, 0 < γ p) ∧ (∀ p, γ p ≤ Fintype.card (κ p)) ∧
      ∀ (ιC : Fin Q.s → Type) [∀ p, Fintype (ιC p)] [∀ p, DecidableEq (ιC p)],
        (∀ p, γ p + Fintype.card (ιC p) = Fintype.card (κ p)) →
        (∀ β, Q.GeneralQuot K ιC β → Q.GeneralQuot K κ β) ∧
        ∃ (V : Q.Rep K ι) (W : Q.Rep K κ), ∀ (V' : Q.Rep K ι) (C' : Q.Rep K ιC),
          Q.extDim V W ≤ Q.extDim V' C' := by
  obtain ⟨γ, hγι, hγκ, hγpos, hquotV, hsubW, V₀, W₀, φ₀, hgen₀, hφ₀, hrank₀⟩ :=
    Q.exists_generalRank (K := K) (ι := ι) (κ := κ)
  refine ⟨γ, hγpos hpos, hγκ, fun ιC _ _ hC => ⟨fun β hβ => hβ.of_generalSub hsubW hC, ?_⟩⟩
  -- the block families
  set ιK : Fin Q.s → Type := finFam fun p => Fintype.card (ι p) - γ p
  set ιI : Fin Q.s → Type := finFam γ
  have hKI : ∀ p, Fintype.card (ιK p) + Fintype.card (ιI p) = Fintype.card (ι p) := fun p => by
    simp only [ιK, ιI, finFam, Fintype.card_fin]
    have := hγι p
    omega
  have hIC : ∀ p, Fintype.card (ιI p) + Fintype.card (ιC p) = Fintype.card (κ p) := fun p => by
    simpa [ιI] using hC p
  -- a hom-generic pair in normal form
  obtain ⟨P, P', -, B₁, y₁, I₁, y₂, C₁, hV₁, hW₁⟩ := Q.exists_normalForm (ιK := ιK) (ιI := ιI)
    (ιC := ιC) hφ₀ (fun p => by simp [ιI, hrank₀ p]) hKI hIC
  have hgen₁ : Q.IsHomGeneric (Q.blockRep B₁ y₁ I₁) (Q.blockRep I₁ y₂ C₁) := by
    rw [← hV₁, ← hW₁]
    exact (Q.isHomGeneric_transport_iff P P' V₀ W₀).mpr hgen₀
  -- a hom-generic pair `([[B, y₁], [0, I]], C)`
  set R : VertexIso K ι fun p => ιK p ⊕ ιI p :=
    VertexIso.ofEquiv fun p => Fintype.equivOfCardEq (by rw [Fintype.card_sum, hKI])
  have hsub : Q.GeneralSub K (fun p => ιK p ⊕ ιI p) (dimVec ιK) := by
    rw [Q.generalSub_iff_generalQuot (β := γ) fun p => by
      simp only [dimVec_apply, Fintype.card_sum, ιI, finFam, Fintype.card_fin]]
    exact (Q.generalQuot_iff_of_vertexIso R).mp hquotV
  obtain ⟨z, ⟨⟨V₂, ⟨S, hS, hdim⟩, hz⟩, -⟩, hgen₂⟩ :=
    (hsub.sumElim (zariskiDense_univ (σ := Q.Entry ιC))).exists_of_eventually
      (Q.eventually_isHomGeneric (K := K) (ι := fun p => ιK p ⊕ ιI p) (κ := ιC))
  have hV₂ : Q.pairFst z = V₂ := by rw [pairFst, ← hz, ofCoord_coord]
  rw [hV₂] at hgen₂
  obtain ⟨P₂, B₂, y₁', I₂, hP₂⟩ := hS.exists_transport_eq_blockRep Q (ι₁ := ιK) (ι₂ := ιI)
    (fun p => by rw [hdim, dimVec_apply]) (fun p => Fintype.card_sum.symm)
  have hgen₂' : Q.IsHomGeneric (Q.blockRep B₂ y₁' I₂) (Q.pairSnd z) := by
    rw [← hP₂, ← Q.transport_refl (Q.pairSnd z)]
    exact (Q.isHomGeneric_transport_iff P₂ (VertexIso.refl K ιC) _ _).mpr hgen₂
  -- a single good normal-form pair
  obtain ⟨B, y, I, y', C, hgenW, hgenC⟩ := exists_normalForm_isHomGeneric_both hgen₁ hgen₂'
  have hext := hgenW.extDim_normalForm
  -- back to the families `ι` and `κ`
  set R' : VertexIso K (fun p => ιI p ⊕ ιC p) κ :=
    VertexIso.ofEquiv fun p => Fintype.equivOfCardEq (by rw [Fintype.card_sum, hIC])
  refine ⟨Q.transport R.symm (Q.blockRep B y I), Q.transport R' (Q.blockRep I y' C),
    fun V' C' => ?_⟩
  rw [extDim_transport, hext]
  calc Q.extDim (Q.blockRep B y I) C
      ≤ Q.extDim (Q.transport R V') (Q.transport (VertexIso.refl K ιC) C') :=
        hgenC.extDim_le _ _
    _ = Q.extDim V' C' := extDim_transport _ _ _ _ _

end Cokernel


end FQuiver

end

end QuiverInvariants
