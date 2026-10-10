import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.StdBasis
import RSCounterexample.QuiverInvariants.Ringel

/-!
# Determinantal semi-invariants

Let `ι` and `κ` be vertex families of a forward quiver with `⟨dim ι, dim κ⟩ = 0`, so that the
Ringel map `d_{V,W} : ⊕_p Hom(K^{ι p}, K^{κ p}) → ⊕_{e : p → q} Hom(K^{ι p}, K^{κ q})` is a map
between spaces of the same dimension. Fixing `V` and an identification `e` of the coordinates,
the determinant `c^V(W) = det d_{V,W}` is a polynomial in `W`: the determinant of the Ringel
matrix of `V` and of the universal representation (Baldoni–Vergne–Walter, Definition 3.5;
Schofield–van den Bergh, Derksen–Weyman).

This file proves that `c^V` is a semi-invariant of weight `L(dim ι)`, where
`L(α)_q = α_q − ∑_p (number of arrows p → q) α_p` (Baldoni–Vergne–Walter, Proposition 3.6), and
that `c^V ≠ 0` as soon as `ext(V, W) = 0` for some `W`.

The determinant is never expanded: `c^V` is `Matrix.det` of a matrix of polynomials, and all
facts about it are proved through evaluation and the multiplicativity of determinants. The
equivariance comes from `d_{V, h · W} = A_h ∘ d_{V,W} ∘ B_h⁻¹`, where `A_h` and `B_h` multiply
by `h` on the left; their determinants are computed with a determinant formula for products of
endomorphisms of a family of spaces (`QuiverInvariants.det_pi_of_family`).

## Main definitions

* `QuiverInvariants.FQuiver.eulerWeight α`: the weight `q ↦ α_q − ∑_p (arrows p q) α_p`.
* `QuiverInvariants.FQuiver.ringelDet V W e`: `det d_{V,W}` in the coordinates identified by `e`.
* `QuiverInvariants.FQuiver.detSemiInvariant V e`: the polynomial `W ↦ ringelDet V W e`.

## Main results

* `QuiverInvariants.det_blockDiagonal'`, `QuiverInvariants.det_pi_of_family`,
  `QuiverInvariants.det_matMulLeft`: determinants of block-diagonal maps.
* `QuiverInvariants.FQuiver.eval_detSemiInvariant`: `c^V(W) = ringelDet V W e`.
* `QuiverInvariants.FQuiver.isSemiInvariant_detSemiInvariant`: `c^V` is a semi-invariant of
  weight `eulerWeight (dim ι)`.
* `QuiverInvariants.FQuiver.detSemiInvariant_ne_zero`: `c^V ≠ 0` if `ext(V, W) = 0`.
* `QuiverInvariants.FQuiver.exists_semiInvariant_of_extDim_eq_zero`: a nonzero semi-invariant of
  weight `eulerWeight (dim ι)` on the representations on `κ`, if `⟨dim ι, dim κ⟩ = 0` and some
  `ext(V, W)` vanishes.
-/

open MvPolynomial

open scoped Matrix

namespace QuiverInvariants

noncomputable section

/-! ### Determinants of block-diagonal maps -/

section BlockDet

/-- The determinant of a block-diagonal matrix whose blocks have varying index types. -/
theorem det_blockDiagonal' {R : Type*} [CommRing R] {α : Type*} [Fintype α] [DecidableEq α]
    {m : α → Type*} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    (d : ∀ a, Matrix (m a) (m a) R) : (Matrix.blockDiagonal' d).det = ∏ a, (d a).det := by
  classical
  let : LinearOrder α := LinearOrder.lift' (Fintype.equivFin α) (Fintype.equivFin α).injective
  rw [(Matrix.blockTriangular_blockDiagonal' d).det_fintype]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Matrix.det_submatrix_equiv_self (Equiv.sigmaSubtype a).symm]
  congr 1
  ext i j
  simp [Matrix.toSquareBlock, Matrix.toSquareBlockProp, Equiv.sigmaSubtype,
    Matrix.blockDiagonal'_apply_eq]

variable {K : Type*} [Field K]

/-- **Determinant of a product of endomorphisms of a family of spaces**: the endomorphism of
`∏ a, M a` acting by `f a` on each factor has determinant `∏ a, det (f a)`. -/
theorem det_pi_of_family {α : Type*} [Fintype α] [DecidableEq α] {M : α → Type*}
    [∀ a, AddCommGroup (M a)] [∀ a, Module K (M a)] [∀ a, FiniteDimensional K (M a)]
    (f : ∀ a, M a →ₗ[K] M a) :
    LinearMap.det (LinearMap.pi fun a => f a ∘ₗ LinearMap.proj a) = ∏ a, LinearMap.det (f a) := by
  classical
  let b : ∀ a, Module.Basis (Module.Free.ChooseBasisIndex K (M a)) K (M a) :=
    fun a => Module.Free.chooseBasis K (M a)
  let B := Pi.basis b
  rw [← LinearMap.det_toMatrix B]
  have hB : LinearMap.toMatrix B B (LinearMap.pi fun a => f a ∘ₗ LinearMap.proj a) =
      Matrix.blockDiagonal' fun a => LinearMap.toMatrix (b a) (b a) (f a) := by
    ext ⟨a, i⟩ ⟨a', j⟩
    rw [LinearMap.toMatrix_apply, Matrix.blockDiagonal'_apply]
    simp only [B, Pi.basis_apply, Pi.basis_repr, LinearMap.pi_apply, LinearMap.comp_apply,
      LinearMap.proj_apply]
    by_cases h : a = a'
    · subst h
      simp [LinearMap.toMatrix_apply]
    · simp [h]
  rw [hB, det_blockDiagonal']
  exact Finset.prod_congr rfl fun a _ => LinearMap.det_toMatrix (b a) (f a)

/-- Left multiplication by a square matrix, on rectangular matrices. -/
def matMulLeft {m n : Type*} [Fintype m] (h : Matrix m m K) : Matrix m n K →ₗ[K] Matrix m n K where
  toFun X := h * X
  map_add' := Matrix.mul_add h
  map_smul' c X := Matrix.mul_smul h c X

@[simp] theorem matMulLeft_apply {m n : Type*} [Fintype m] (h : Matrix m m K)
    (X : Matrix m n K) : matMulLeft h X = h * X :=
  rfl

/-- Left multiplication by `h` on `m × n` matrices has determinant `det h ^ |n|`. -/
theorem det_matMulLeft {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (h : Matrix m m K) : LinearMap.det (matMulLeft (n := n) h) = h.det ^ Fintype.card n := by
  let T : Matrix m n K ≃ₗ[K] (n → m → K) := Matrix.transposeLinearEquiv m n K K
  have hT : (T : Matrix m n K →ₗ[K] (n → m → K)) ∘ₗ matMulLeft h ∘ₗ
      (T.symm : (n → m → K) →ₗ[K] Matrix m n K) =
        LinearMap.pi fun j : n => Matrix.toLin' h ∘ₗ LinearMap.proj j := by
    refine LinearMap.ext fun Y => funext fun j => funext fun i => ?_
    change (h * (Y : Matrix n m K)ᵀ) i j = (h *ᵥ Y j) i
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rfl
  rw [← LinearMap.det_conj (matMulLeft h) T, hT, LinearMap.det_pi, LinearMap.det_toLin',
    Finset.prod_const, Finset.card_univ]

end BlockDet

/-! ### The Ringel determinant -/

namespace FQuiver

variable (Q : FQuiver)

/-- The weight `L(α)_q = α_q − ∑_p (number of arrows p → q) α_p`; its pairing with `β` is the
Euler form `⟨α, β⟩`. -/
def eulerWeight (α : Fin Q.s → ℤ) (q : Fin Q.s) : ℤ :=
  α q - ∑ p, (Q.arrows p q : ℤ) * α p

/-- The pairing of `eulerWeight α` with `β` is the Euler form. -/
theorem sum_eulerWeight_mul (α β : Fin Q.s → ℤ) :
    ∑ q, Q.eulerWeight α q * β q = Q.euler α β := by
  simp only [eulerWeight, euler, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  congr 1
  rw [Fintype.sum_sigma, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
  simp [src, tgt, mul_assoc]

variable {K : Type*} [Field K] {ι κ : Fin Q.s → Type} [∀ p, Fintype (ι p)]
  [∀ p, DecidableEq (ι p)] [∀ p, Fintype (κ p)] [∀ p, DecidableEq (κ p)]

/-- The determinant of the Ringel map `d_{V,W}`, with the coordinates of its target identified
with those of its source by `e`. -/
def ringelDet (V : Q.Rep K ι) (W : Q.Rep K κ) (e : VertexEntry ι κ ≃ Q.ArrowEntry ι κ) : K :=
  ((Q.ringelMatrix V W).submatrix e id).det

/-- The identification of arrow data with vertex data given by `e`. -/
def entryEquiv (e : VertexEntry ι κ ≃ Q.ArrowEntry ι κ) :
    Q.ArrowHom K ι κ ≃ₗ[K] VertexHom K ι κ :=
  (Q.arrowCoord K ι κ).trans ((LinearEquiv.funCongrLeft K K e).trans (vertexCoord K ι κ).symm)

/-- The Ringel determinant is the determinant of an endomorphism of `VertexHom K ι κ`. -/
theorem ringelDet_eq_det (V : Q.Rep K ι) (W : Q.Rep K κ)
    (e : VertexEntry ι κ ≃ Q.ArrowEntry ι κ) :
    Q.ringelDet V W e = LinearMap.det ((Q.entryEquiv e).toLinearMap ∘ₗ Q.ringel V W) := by
  rw [← LinearMap.det_conj _ (vertexCoord K ι κ), ← LinearMap.det_toMatrix', ringelDet]
  congr 1

/-- Left multiplication by `h` on vertex data. -/
theorem vertexConj_refl_ofGL (h : GLFamily K κ) :
    (vertexConj (VertexIso.refl K ι) (VertexIso.ofGL h)).toLinearMap =
      LinearMap.pi fun p => matMulLeft (n := ι p) (h p : Matrix (κ p) (κ p) K) ∘ₗ
        LinearMap.proj p := by
  refine LinearMap.ext fun ψ => funext fun p => ?_
  simp

/-- Left multiplication by `h` on arrow data. -/
theorem arrowConj_refl_ofGL (h : GLFamily K κ) :
    (Q.arrowConj (VertexIso.refl K ι) (VertexIso.ofGL h)).toLinearMap =
      LinearMap.pi fun e => matMulLeft (n := ι (Q.src e))
        (h (Q.tgt e) : Matrix (κ (Q.tgt e)) (κ (Q.tgt e)) K) ∘ₗ LinearMap.proj e := by
  refine LinearMap.ext fun X => funext fun e => ?_
  simp

theorem det_vertexConj_refl_ofGL (h : GLFamily K κ) :
    LinearMap.det (vertexConj (VertexIso.refl K ι) (VertexIso.ofGL h)).toLinearMap =
      ∏ p, (h p : Matrix (κ p) (κ p) K).det ^ Fintype.card (ι p) := by
  rw [vertexConj_refl_ofGL, det_pi_of_family]
  exact Finset.prod_congr rfl fun p _ => det_matMulLeft _

theorem det_arrowConj_refl_ofGL (h : GLFamily K κ) :
    LinearMap.det (Q.arrowConj (VertexIso.refl K ι) (VertexIso.ofGL h)).toLinearMap =
      ∏ e : Q.Arrow, (h (Q.tgt e) : Matrix (κ (Q.tgt e)) (κ (Q.tgt e)) K).det ^
        Fintype.card (ι (Q.src e)) := by
  rw [arrowConj_refl_ofGL, det_pi_of_family]
  exact Finset.prod_congr rfl fun e _ => det_matMulLeft _

/-- **Equivariance of the Ringel determinant**:
`det d_{V, h · W} = det A_h · det d_{V,W} · (det B_h)⁻¹`. -/
theorem ringelDet_act (V : Q.Rep K ι) (W : Q.Rep K κ) (h : GLFamily K κ)
    (e : VertexEntry ι κ ≃ Q.ArrowEntry ι κ) :
    Q.ringelDet V (Q.act h W) e =
      (∏ a : Q.Arrow, (h (Q.tgt a) : Matrix (κ (Q.tgt a)) (κ (Q.tgt a)) K).det ^
          Fintype.card (ι (Q.src a))) *
        Q.ringelDet V W e *
          (∏ p, (h p : Matrix (κ p) (κ p) K).det ^ Fintype.card (ι p))⁻¹ := by
  set A := (Q.arrowConj (VertexIso.refl K ι) (VertexIso.ofGL h)).toLinearMap
  set B := vertexConj (VertexIso.refl K ι) (VertexIso.ofGL h)
  set ε := Q.entryEquiv (K := K) e with hε
  have hR : Q.ringel V (Q.act h W) = A ∘ₗ Q.ringel V W ∘ₗ B.symm.toLinearMap := by
    have := Q.ringel_transport (VertexIso.refl K ι) (VertexIso.ofGL h) V W
    rwa [transport_refl, ← act_eq_transport] at this
  have hsplit : ε.toLinearMap ∘ₗ Q.ringel V (Q.act h W) =
      (ε.toLinearMap ∘ₗ A ∘ₗ ε.symm.toLinearMap) ∘ₗ (ε.toLinearMap ∘ₗ Q.ringel V W) ∘ₗ
        B.symm.toLinearMap := by
    rw [hR]
    ext ψ
    simp
  have hB : LinearMap.det B.symm.toLinearMap * LinearMap.det B.toLinearMap = 1 := by
    rw [← LinearMap.det_comp, show B.symm.toLinearMap ∘ₗ B.toLinearMap = LinearMap.id from
      LinearMap.ext fun ψ => B.symm_apply_apply ψ, LinearMap.det_id]
  have hB' : LinearMap.det B.symm.toLinearMap = (LinearMap.det B.toLinearMap)⁻¹ :=
    eq_inv_of_mul_eq_one_left hB
  rw [ringelDet_eq_det, ringelDet_eq_det, hsplit, LinearMap.det_comp, LinearMap.det_comp,
    LinearMap.det_conj, hB', det_arrowConj_refl_ofGL, det_vertexConj_refl_ofGL, hε]
  ring

omit [∀ p, DecidableEq (ι p)] in
/-- The determinants of `A_h` and `B_h` combine to the character `χ_σ(h)⁻¹` with
`σ = eulerWeight (dim ι)`. -/
theorem prod_det_mul_inv_eq_chi (h : GLFamily K κ) :
    (∏ a : Q.Arrow, (h (Q.tgt a) : Matrix (κ (Q.tgt a)) (κ (Q.tgt a)) K).det ^
        Fintype.card (ι (Q.src a))) *
        (∏ p, (h p : Matrix (κ p) (κ p) K).det ^ Fintype.card (ι p))⁻¹ =
      (((chi (Q.eulerWeight fun p => (Fintype.card (ι p) : ℤ)) h)⁻¹ : Kˣ) : K) := by
  set u : Fin Q.s → Kˣ := fun p => Matrix.GeneralLinearGroup.det (h p) with hu_def
  have hu : ∀ p, (h p : Matrix (κ p) (κ p) K).det = (u p : K) := fun p =>
    (Matrix.GeneralLinearGroup.val_det_apply (h p)).symm
  have hterm : ∀ pq : Fin Q.s × Fin Q.s,
      ∏ b : Fin (Q.arrows pq.1 pq.2), u (Q.tgt ⟨pq, b⟩) ^ Fintype.card (ι (Q.src ⟨pq, b⟩)) =
        u pq.2 ^ (Q.arrows pq.1 pq.2 * Fintype.card (ι pq.1)) := fun pq => by
    calc ∏ b : Fin (Q.arrows pq.1 pq.2), u (Q.tgt ⟨pq, b⟩) ^ Fintype.card (ι (Q.src ⟨pq, b⟩))
        = ∏ _b : Fin (Q.arrows pq.1 pq.2), u pq.2 ^ Fintype.card (ι pq.1) := rfl
      _ = u pq.2 ^ (Q.arrows pq.1 pq.2 * Fintype.card (ι pq.1)) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul']
  have harrows : ∏ a : Q.Arrow, u (Q.tgt a) ^ Fintype.card (ι (Q.src a)) =
      ∏ q, u q ^ (∑ p, Q.arrows p q * Fintype.card (ι p)) := by
    rw [Fintype.prod_sigma, Finset.prod_congr rfl fun pq _ => hterm pq, Fintype.prod_prod_type,
      Finset.prod_comm]
    exact Finset.prod_congr rfl fun q _ =>
      Finset.prod_pow_eq_pow_sum Finset.univ (fun p => Q.arrows p q * Fintype.card (ι p)) (u q)
  have hchi : chi (Q.eulerWeight fun p => (Fintype.card (ι p) : ℤ)) h =
      (∏ q, u q ^ Fintype.card (ι q)) *
        (∏ q, u q ^ (∑ p, Q.arrows p q * Fintype.card (ι p)))⁻¹ := by
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, chi]
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [eulerWeight, zpow_sub, zpow_natCast]
    congr 2
    rw [← zpow_natCast]
    push_cast
    rfl
  have hunits : (∏ a : Q.Arrow, u (Q.tgt a) ^ Fintype.card (ι (Q.src a))) *
      (∏ p, u p ^ Fintype.card (ι p))⁻¹ =
        (chi (Q.eulerWeight fun p => (Fintype.card (ι p) : ℤ)) h)⁻¹ := by
    rw [harrows, hchi, mul_inv_rev, inv_inv]
  simp only [hu]
  rw [← hunits]
  push_cast
  rfl

/-- **Equivariance of the Ringel determinant** in terms of the character. -/
theorem ringelDet_act_eq_chi (V : Q.Rep K ι) (W : Q.Rep K κ) (h : GLFamily K κ)
    (e : VertexEntry ι κ ≃ Q.ArrowEntry ι κ) :
    Q.ringelDet V (Q.act h W) e =
      (((chi (Q.eulerWeight fun p => (Fintype.card (ι p) : ℤ)) h)⁻¹ : Kˣ) : K) *
        Q.ringelDet V W e := by
  rw [Q.ringelDet_act V W h e, ← Q.prod_det_mul_inv_eq_chi h]
  ring

/-- **Nonvanishing.** If `ext(V, W) = 0`, the Ringel map is surjective between spaces of the same
dimension, so its determinant does not vanish. -/
theorem ringelDet_ne_zero {V : Q.Rep K ι} {W : Q.Rep K κ} (hext : Q.extDim V W = 0)
    (e : VertexEntry ι κ ≃ Q.ArrowEntry ι κ) : Q.ringelDet V W e ≠ 0 := by
  rw [ringelDet_eq_det]
  have hsurj : Function.Surjective (Q.ringel V W) := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    have h₁ := Q.extDim_add_ringelRank V W
    rw [hext, zero_add] at h₁
    rw [Q.finrank_arrowHom]
    exact h₁
  have hsurj' : Function.Surjective ((Q.entryEquiv e).toLinearMap ∘ₗ Q.ringel V W) :=
    (Q.entryEquiv e).surjective.comp hsurj
  have hinj := LinearMap.injective_iff_surjective.mpr hsurj'
  exact fun h0 => LinearMap.det_eq_zero_iff_ker_ne_bot.mp h0 (LinearMap.ker_eq_bot.mpr hinj)

/-! ### The determinantal semi-invariant -/

/-- The **determinantal semi-invariant** `c^V`: the polynomial `W ↦ det d_{V,W}` on the
representations on `κ`. -/
def detSemiInvariant (V : Q.Rep K ι) (e : VertexEntry ι κ ≃ Q.ArrowEntry ι κ) :
    MvPolynomial (Q.Entry κ) K :=
  ((Q.ringelMatrix (Q.mapArrowHom C V) (Q.univRep K κ)).submatrix e id).det

theorem eval_detSemiInvariant (V : Q.Rep K ι) (W : Q.Rep K κ)
    (e : VertexEntry ι κ ≃ Q.ArrowEntry ι κ) :
    eval (Q.coord W) (Q.detSemiInvariant V e) = Q.ringelDet V W e := by
  have hV : Q.mapArrowHom (eval (Q.coord W)) (Q.mapArrowHom C V) = V := by
    funext a
    ext j i
    simp
  rw [detSemiInvariant, RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map,
    ringelMatrix_map, hV, mapArrowHom_eval_coord_univRep]
  rfl

/-- **`c^V` is a semi-invariant of weight `eulerWeight (dim ι)`** (Baldoni–Vergne–Walter,
Proposition 3.6). -/
theorem isSemiInvariant_detSemiInvariant (V : Q.Rep K ι)
    (e : VertexEntry ι κ ≃ Q.ArrowEntry ι κ) :
    Q.IsSemiInvariant (Q.eulerWeight fun p => (Fintype.card (ι p) : ℤ))
      (Q.detSemiInvariant V e) := fun h W => by
  rw [eval_detSemiInvariant, eval_detSemiInvariant, ringelDet_act_eq_chi]

/-- `c^V ≠ 0` if `ext(V, W) = 0` for some `W`. -/
theorem detSemiInvariant_ne_zero {V : Q.Rep K ι} {W : Q.Rep K κ} (hext : Q.extDim V W = 0)
    (e : VertexEntry ι κ ≃ Q.ArrowEntry ι κ) : Q.detSemiInvariant V e ≠ 0 := fun h0 =>
  Q.ringelDet_ne_zero hext e (by rw [← eval_detSemiInvariant, h0, map_zero])

omit [∀ p, DecidableEq (ι p)] [∀ p, DecidableEq (κ p)] in
/-- The coordinates of vertex data and of arrow data are equinumerous when the Euler form
vanishes. -/
theorem card_vertexEntry_eq_card_arrowEntry
    (heuler : Q.euler (fun p => (Fintype.card (ι p) : ℤ)) (fun p => (Fintype.card (κ p) : ℤ)) =
      0) :
    Fintype.card (VertexEntry ι κ) = Fintype.card (Q.ArrowEntry ι κ) := by
  simp only [euler, sub_eq_zero] at heuler
  simp only [Fintype.card_sigma, Fintype.card_prod]
  exact_mod_cast heuler

/-- **A determinantal semi-invariant.** If `⟨dim ι, dim κ⟩ = 0` and `ext(V, W) = 0` for some
`V` on `ι` and `W` on `κ`, then the representations on `κ` have a nonzero semi-invariant of
weight `eulerWeight (dim ι)`. -/
theorem exists_semiInvariant_of_extDim_eq_zero
    (heuler : Q.euler (fun p => (Fintype.card (ι p) : ℤ)) (fun p => (Fintype.card (κ p) : ℤ)) =
      0) {V : Q.Rep K ι} {W : Q.Rep K κ} (hext : Q.extDim V W = 0) :
    ∃ f : MvPolynomial (Q.Entry κ) K, f ≠ 0 ∧
      Q.IsSemiInvariant (Q.eulerWeight fun p => (Fintype.card (ι p) : ℤ)) f :=
  let e := Fintype.equivOfCardEq (Q.card_vertexEntry_eq_card_arrowEntry heuler)
  ⟨Q.detSemiInvariant V e, Q.detSemiInvariant_ne_zero hext e,
    Q.isSemiInvariant_detSemiInvariant V e⟩

end FQuiver

end

end QuiverInvariants
