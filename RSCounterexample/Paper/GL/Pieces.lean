import RSCounterexample.Paper.GL.CoordinateRing

/-!
# Polynomiality and characters of the graded pieces of `R_Q`

The graded piece of multidegree `ℓ` of the coordinate ring `R_Q` is a rational representation of
`L = ∏_p GL(V_p)`: `g_q⁻¹` enters its matrix coefficients `in_q(ℓ) = ∑_{e : · → q} ℓ_e` times.
Twisted by `∏_q det(g_q)^{c_q}` with every `c_q ≥ in_q(ℓ)` it becomes polynomial, since
`det(g_q) g_q⁻¹ = adj(g_q)`. Its character is the character `∏_e h_{ℓ_e}(x_i/x_j)` of the piece
times `∏_q (∏_{i ∈ I_q} x_i)^{c_q}`, an ordinary polynomial.

## Main statements

* `Schubert.RS.GL.laurentEval`: evaluation of Laurent polynomials at a point of the torus;
  `laurentEval_toLaurent` compares it with polynomial evaluation.
* `Schubert.RS.Quiver.ForwardQuiver.gradedCharacter_eq_sum_monomials`: `∏_e h_{ℓ_e}(x_i/x_j)` is
  the sum of the weights of the monomials of multidegree `ℓ`.
* `Schubert.RS.Quiver.ForwardQuiver.isPolynomialLeviRep_twist_coordPiece`.
* `Schubert.RS.Quiver.ForwardQuiver.twistedPieceCharacter`,
  `isLeviCharacter_twist_coordPiece`, `toLaurent_twistedPieceCharacter`.
-/

namespace Schubert.RS.GL

noncomputable section

open MvPolynomial

variable {n : ℕ}

/-- The character `μ ↦ ∏_k t_k^{μ_k}` of the weight lattice at a point `t` of the torus. -/
def torusCharacter (t : Fin n → ℂˣ) : Multiplicative (Weight n) →* ℂ where
  toFun μ := ((∏ k, t k ^ (Multiplicative.toAdd μ k) : ℂˣ) : ℂ)
  map_one' := by simp
  map_mul' μ ν := by simp [zpow_add, Finset.prod_mul_distrib]

/-- Evaluation of Laurent polynomials at a point `t` of the torus. -/
def laurentEval (t : Fin n → ℂˣ) : Laurent n →ₐ[ℤ] ℂ :=
  AddMonoidAlgebra.lift ℤ ℂ (Weight n) (torusCharacter t)

theorem laurentEval_single (t : Fin n → ℂˣ) (μ : Weight n) (r : ℤ) :
    laurentEval t (AddMonoidAlgebra.single μ r) = r * ((∏ k, t k ^ μ k : ℂˣ) : ℂ) := by
  rw [laurentEval, AddMonoidAlgebra.lift_single, zsmul_eq_mul]
  rfl

theorem prod_zpow_single (t : Fin n → ℂˣ) (a : Fin n) :
    ∏ k, t k ^ (Pi.single a (1 : ℤ) : Weight n) k = t a := by
  rw [Finset.prod_eq_single a (fun k _ hk => by rw [Pi.single_eq_of_ne hk, zpow_zero])
    (by simp), Pi.single_eq_same, zpow_one]

/-- **Evaluating a polynomial as a Laurent polynomial is evaluating it.** -/
theorem laurentEval_toLaurent (t : Fin n → ℂˣ) (P : Schubert.RS.Polynomial n) :
    laurentEval t (toLaurent P) = eval₂ (Int.castRingHom ℂ) (fun i => (t i : ℂ)) P := by
  have h : ((laurentEval t : Laurent n →+* ℂ).comp toLaurent) =
      eval₂Hom (Int.castRingHom ℂ) fun i => (t i : ℂ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      have hCa : toLaurent (C a : Schubert.RS.Polynomial n) = AddMonoidAlgebra.single 0 a := by
        rw [← monomial_zero', toLaurent_monomial, map_zero]
      rw [RingHom.comp_apply, hCa, coe_eval₂Hom, eval₂_C, RingHom.coe_coe, laurentEval_single]
      simp
    · intro i
      rw [RingHom.comp_apply, X, toLaurent_monomial, coe_eval₂Hom, eval₂_monomial,
        RingHom.coe_coe, laurentEval_single]
      have hw : exponentWeight (Finsupp.single i 1) = (Pi.single i 1 : Weight n) := by
        funext k
        by_cases hk : k = i
        · subst hk
          simp [exponentWeight]
        · simp [exponentWeight, hk]
      rw [hw, prod_zpow_single]
      simp
  exact RingHom.congr_fun h P

end

end Schubert.RS.GL

namespace Schubert.RS.Quiver.ForwardQuiver

noncomputable section

open Matrix MvPolynomial Schubert.RS.GL
open scoped Kronecker

variable (Q : ForwardQuiver)

/-! ### Degrees of monomials -/

/-- The coordinates of the arrows satisfying a condition carry the corresponding part of the
multidegree. -/
theorem sum_filter_arrow {ℓ : Q.Arrow → ℕ} {m : Q.ArrowEntry →₀ ℕ} (hm : m ∈ Q.pieceSet ℓ)
    (P : Q.Arrow → Prop) [DecidablePred P] :
    ∑ v ∈ Finset.univ.filter (fun v : Q.ArrowEntry => P v.1), m v =
      ∑ e ∈ Finset.univ.filter P, ℓ e := by
  rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h : P e
  · simp only [h, ite_true]
    rw [← weight_arrowGrading_apply, (Q.mem_pieceSet).mp hm]
  · simp [h]

theorem prod_pow_tgt {M : Type*} [CommMonoid M] {ℓ : Q.Arrow → ℕ} {m : Q.ArrowEntry →₀ ℕ}
    (hm : m ∈ Q.pieceSet ℓ) (x : Fin Q.s → M) :
    ∏ v, x (Q.tgt v.1) ^ m v = ∏ q, x q ^ Q.inDegree ℓ q := by
  rw [← Finset.prod_fiberwise Finset.univ (fun v : Q.ArrowEntry => Q.tgt v.1)]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [Finset.prod_congr rfl fun v hv => by rw [(Finset.mem_filter.mp hv).2],
    Finset.prod_pow_eq_pow_sum]
  exact congrArg _ (Q.sum_filter_arrow hm fun e => Q.tgt e = q)

theorem prod_pow_src {M : Type*} [CommMonoid M] {ℓ : Q.Arrow → ℕ} {m : Q.ArrowEntry →₀ ℕ}
    (hm : m ∈ Q.pieceSet ℓ) (x : Fin Q.s → M) :
    ∏ v, x (Q.src v.1) ^ m v = ∏ p, x p ^ Q.outDegree ℓ p := by
  rw [← Finset.prod_fiberwise Finset.univ (fun v : Q.ArrowEntry => Q.src v.1)]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [Finset.prod_congr rfl fun v hv => by rw [(Finset.mem_filter.mp hv).2],
    Finset.prod_pow_eq_pow_sum]
  exact congrArg _ (Q.sum_filter_arrow hm fun e => Q.src e = p)

/-! ### Polynomiality of the twisted pieces -/

/-- The polynomial ring in the matrix entries of the blocks of `L`. -/
abbrev LeviCoord : Type := MvPolynomial (Σ p : Fin Q.s, Fin (Q.dim p) × Fin (Q.dim p)) ℂ

/-- Evaluation of a polynomial in the matrix entries at `g ∈ L`. -/
def evalLevi (g : LeviGroup Q.dim) : Q.LeviCoord →ₐ[ℂ] ℂ :=
  aeval fun x => (g x.1 : Matrix (Fin (Q.dim x.1)) (Fin (Q.dim x.1)) ℂ) x.2.1 x.2.2

/-- The generic matrix of block `p`. -/
def genericBlock (p : Fin Q.s) : Matrix (Fin (Q.dim p)) (Fin (Q.dim p)) Q.LeviCoord :=
  fun a b => X ⟨p, (a, b)⟩

theorem map_genericBlock (g : LeviGroup Q.dim) (p : Fin Q.s) :
    (Q.evalLevi g).mapMatrix (Q.genericBlock p) = (g p : Matrix _ _ ℂ) := by
  ext a b
  simp [genericBlock, evalLevi]

theorem adjugate_units {k : ℕ} (u : GL (Fin k) ℂ) :
    adjugate (u : Matrix (Fin k) (Fin k) ℂ) =
      (u : Matrix (Fin k) (Fin k) ℂ).det • ((u⁻¹ : GL (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ) := by
  calc adjugate (u : Matrix (Fin k) (Fin k) ℂ)
      = ((u⁻¹ : GL (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ) * (u : Matrix (Fin k) (Fin k) ℂ) *
          adjugate (u : Matrix (Fin k) (Fin k) ℂ) := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    _ = _ := by rw [mul_assoc, mul_adjugate, mul_smul_comm, mul_one]

/-- The generic coordinate matrix: `coordMatrix` with `g_q⁻¹` replaced by `adj(g_q)`. -/
def genericCoordMatrix : Matrix Q.ArrowEntry Q.ArrowEntry Q.LeviCoord :=
  blockDiagonal' fun e => Q.genericBlock (Q.src e) ⊗ₖ (adjugate (Q.genericBlock (Q.tgt e)))ᵀ

/-- At `g`, the generic coordinate matrix is `coordMatrix g` with the column of `X ⟨e, _⟩` scaled
by `det(g_q)`, `q` the target of `e`. -/
theorem map_genericCoordMatrix (g : LeviGroup Q.dim) :
    Q.genericCoordMatrix.map (Q.evalLevi g) =
      Q.coordMatrix g * diagonal fun v => (g (Q.tgt v.1)).val.det := by
  ext ⟨e, a⟩ ⟨e', b⟩
  rw [Matrix.map_apply, Matrix.mul_diagonal]
  by_cases h : e = e'
  · subst h
    have h1 := congrFun (congrFun (Q.map_genericBlock g (Q.src e)) a.1) b.1
    have h2 := congrFun (congrFun ((Q.evalLevi g).map_adjugate (Q.genericBlock (Q.tgt e))) b.2) a.2
    rw [Q.map_genericBlock g, adjugate_units] at h2
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply] at h1 h2
    rw [genericCoordMatrix, blockDiagonal'_apply_eq, kroneckerMap_apply, transpose_apply, map_mul,
      h1, h2, coordMatrix_apply_same, Matrix.smul_apply, smul_eq_mul]
    ring
  · rw [genericCoordMatrix, blockDiagonal'_apply_ne _ _ _ h, map_zero,
      Q.coordMatrix_apply_ne g (u := ⟨e, a⟩) (v := ⟨e', b⟩) h, zero_mul]

/-- The generic coordinate substitution, with coefficients polynomial in the entries of `g`. -/
def genericSubst : Q.coordRing →ₐ[ℂ] MvPolynomial Q.ArrowEntry Q.LeviCoord :=
  aeval fun v => ∑ w, C (Q.genericCoordMatrix w v) * X w

theorem map_genericSubst (g : LeviGroup Q.dim) (φ : Q.coordRing) :
    MvPolynomial.map (Q.evalLevi g : Q.LeviCoord →+* ℂ) (Q.genericSubst φ) =
      linearSubst (Q.genericCoordMatrix.map (Q.evalLevi g)) φ := by
  have h : (mapAlgHom (Q.evalLevi g)).comp Q.genericSubst =
      linearSubst (Q.genericCoordMatrix.map (Q.evalLevi g)) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [genericSubst, smul_eq_C_mul]
  exact AlgHom.congr_fun h φ

/-- **The generic substitution evaluates to `∏_q det(g_q)^{in_q(ℓ)}` times the action of `g`** on
a monomial of multidegree `ℓ`. -/
theorem evalLevi_coeff_genericSubst (g : LeviGroup Q.dim) {ℓ : Q.Arrow → ℕ}
    {m : Q.ArrowEntry →₀ ℕ} (hm : m ∈ Q.pieceSet ℓ) (m' : Q.ArrowEntry →₀ ℕ) :
    Q.evalLevi g ((Q.genericSubst (monomial m 1)).coeff m') =
      (∏ q, (g q).val.det ^ Q.inDegree ℓ q) *
        (Q.coordRep g (monomial m 1)).coeff m' := by
  have h := MvPolynomial.coeff_map (Q.evalLevi g : Q.LeviCoord →+* ℂ)
    (Q.genericSubst (monomial m 1)) m'
  rw [map_genericSubst, map_genericCoordMatrix, linearSubst_mul, AlgHom.comp_apply,
    linearSubst_diagonal_monomial, map_smul, ← coordRep_apply, coeff_smul, smul_eq_mul,
    Q.prod_pow_tgt hm fun q => (g q).val.det] at h
  exact h.symm

/-- The polynomial matrix coefficients of a twisted graded piece in the monomial basis. -/
def piecePoly (ℓ : Q.Arrow → ℕ) (c : Fin Q.s → ℕ) (m' m : Q.pieceSet ℓ) : Q.LeviCoord :=
  (Q.genericSubst (monomial (m : Q.ArrowEntry →₀ ℕ) 1)).coeff (m' : Q.ArrowEntry →₀ ℕ) *
    ∏ q, blockDetPoly Q.dim q ^ (c q - Q.inDegree ℓ q)

/-- The graded piece of multidegree `ℓ` twisted by `∏_q det_q^{c_q}`. -/
abbrev twistedPiece (ℓ : Q.Arrow → ℕ) (c : Fin Q.s → ℕ) :
    _root_.Representation ℂ (LeviGroup Q.dim) (TensorProduct ℂ (Q.coordPiece ℓ).toSubmodule ℂ) :=
  leviTwist Q.dim (Q.coordPiece ℓ).toRepresentation fun q => (c q : ℤ)

/-- **Twisted by `∏_q det_q^{c_q}` with `c_q ≥ in_q(ℓ)`, the graded piece of multidegree `ℓ` is a
polynomial representation.** -/
theorem isPolynomialLeviRep_twist_coordPiece (ℓ : Q.Arrow → ℕ) (c : Fin Q.s → ℕ)
    (hc : ∀ q, Q.inDegree ℓ q ≤ c q) :
    IsPolynomialLeviRep (W := TensorProduct ℂ (Q.coordPiece ℓ).toSubmodule ℂ) Q.dim
      (Q.twistedPiece ℓ c) := by
  classical
  refine isPolynomialLeviRep_of_basis Q.dim
    ((Q.pieceBasis ℓ).map (TensorProduct.rid ℂ _).symm) (Q.piecePoly ℓ c) fun g m' m => ?_
  have he : ∀ P : Q.LeviCoord,
      MvPolynomial.eval (fun x => (g x.1 : Matrix (Fin (Q.dim x.1)) (Fin (Q.dim x.1)) ℂ)
        x.2.1 x.2.2) P = Q.evalLevi g P := fun _ => rfl
  have hχ : ((leviDetCharacter Q.dim (fun q => (c q : ℤ)) g : ℂˣ) : ℂ) =
      ∏ q, (g q).val.det ^ c q := by
    rw [leviDetCharacter_apply, Units.coe_prod]
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [zpow_natCast, Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_det_apply]
  rw [toMatrix_leviTwist, toMatrix_pieceBasis, he, piecePoly, map_mul,
    Q.evalLevi_coeff_genericSubst g m.2, map_prod, hχ]
  simp only [map_pow, ← he, eval_blockDetPoly]
  rw [mul_right_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [← pow_add, Nat.add_sub_cancel' (hc q)]

/-! ### Characters of the twisted pieces -/

/-- The weight `∑_v m_v (e_i − e_j)` of the monomial `X^m`, `v = ⟨e, (i, j)⟩`. -/
def pieceWeight (m : Q.ArrowEntry →₀ ℕ) : Schubert.RS.Weight Q.n :=
  ∑ v, m v • positiveRoot (Q.pos (Q.src v.1) v.2.1) (Q.pos (Q.tgt v.1) v.2.2)

theorem single_pieceWeight (m : Q.ArrowEntry →₀ ℕ) :
    (AddMonoidAlgebra.single (Q.pieceWeight m) (1 : ℤ) : Laurent Q.n) =
      ∏ v, Q.arrowMonomial v.1 v.2 ^ m v := by
  simp only [arrowMonomial, AddMonoidAlgebra.single_pow, one_pow, AddMonoidAlgebra.prod_single,
    Finset.prod_const_one, pieceWeight]

theorem laurentEval_arrowMonomial (t : Fin Q.n → ℂˣ) (v : Q.ArrowEntry) :
    laurentEval t (Q.arrowMonomial v.1 v.2) = Q.entryWeight t v := by
  rw [arrowMonomial, laurentEval_single, Int.cast_one, one_mul, positiveRoot]
  simp only [Pi.sub_apply, zpow_sub, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
    prod_zpow_single]
  rw [entryWeight, Units.val_mul]

theorem laurentEval_single_pieceWeight (t : Fin Q.n → ℂˣ) (m : Q.ArrowEntry →₀ ℕ) :
    laurentEval t (AddMonoidAlgebra.single (Q.pieceWeight m) 1) = ∏ v, Q.entryWeight t v ^ m v := by
  rw [single_pieceWeight, map_prod]
  simp only [map_pow, laurentEval_arrowMonomial]

/-- `h_N(f) = ∑_{s ∈ Sym^N} ∏_a f_a^{mult_s(a)}`. -/
theorem aeval_hsymm {τ R A : Type*} [Fintype τ] [DecidableEq τ] [CommSemiring R] [CommSemiring A]
    [Algebra R A] (f : τ → A) (N : ℕ) :
    aeval f (hsymm τ R N) = ∑ s : Sym τ N, ∏ a, f a ^ (s : Multiset τ).count a := by
  rw [hsymm, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_multiset_prod, Multiset.map_map]
  have hf : (⇑(aeval f) ∘ (X : τ → MvPolynomial τ R)) = f := funext fun a => aeval_X f a
  rw [hf, Finset.prod_multiset_map_count]
  exact Finset.prod_subset (Finset.subset_univ _) fun a _ ha => by
    rw [Multiset.count_eq_zero.mpr (by simpa using ha), pow_zero]

/-- The exponents of multidegree `ℓ`, split by arrows. -/
def pieceEquiv (ℓ : Q.Arrow → ℕ) :
    Q.pieceSet ℓ ≃ ((e : Q.Arrow) →
      {P : Fin (Q.dim (Q.src e)) × Fin (Q.dim (Q.tgt e)) → ℕ // ∑ a, P a = ℓ e}) where
  toFun m e := ⟨fun a => (m : Q.ArrowEntry →₀ ℕ) ⟨e, a⟩, by
    rw [← weight_arrowGrading_apply, (Q.mem_pieceSet).mp m.2]⟩
  invFun x := ⟨Finsupp.equivFunOnFinite.symm fun v => (x v.1).1 v.2, by
    rw [mem_pieceSet]
    funext e
    rw [weight_arrowGrading_apply]
    simpa using (x e).2⟩
  left_inv m := by
    ext v
    simp
  right_inv x := by
    funext e
    ext a
    simp

/-- **The character of a graded piece:** `∏_e h_{ℓ_e}(x_i/x_j)` is the sum of the weights of the
monomials of multidegree `ℓ`. -/
theorem gradedCharacter_eq_sum_monomials (ℓ : Q.Arrow → ℕ) :
    Q.gradedCharacter ℓ =
      ∑ m : Q.pieceSet ℓ, AddMonoidAlgebra.single (Q.pieceWeight (m : Q.ArrowEntry →₀ ℕ)) 1 := by
  classical
  rw [gradedCharacter]
  simp only [aeval_hsymm]
  rw [Finset.prod_univ_sum]
  rw [Fintype.piFinset_univ]
  symm
  refine Fintype.sum_equiv ((Q.pieceEquiv ℓ).trans
    (Equiv.piCongrRight fun e => (Sym.equivNatSumOfFintype _ (ℓ e)).symm)) _ _ fun m => ?_
  rw [single_pieceWeight, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun e _ => Finset.prod_congr rfl fun a _ => ?_
  congr 1
  have h := congrArg (fun P : {P : Fin (Q.dim (Q.src e)) × Fin (Q.dim (Q.tgt e)) → ℕ //
      ∑ a, P a = ℓ e} => P.1 a)
    ((Sym.equivNatSumOfFintype _ (ℓ e)).apply_symm_apply ((Q.pieceEquiv ℓ m) e))
  simp only [Sym.coe_equivNatSumOfFintype_apply_apply] at h
  rw [Equiv.trans_apply, Equiv.piCongrRight_apply, Pi.map_apply, h]
  rfl

/-- The exponent of `∏_q (∏_{i ∈ I_q} x_i)^{c_q} · X^m`'s weight, an ordinary exponent when
`c_q ≥ in_q(ℓ)`. -/
def pieceExponent (c : Fin Q.s → ℕ) (m : Q.ArrowEntry →₀ ℕ) : Fin Q.n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun k =>
    (exponentWeight (blockDetExponent Q.dim c) k + Q.pieceWeight m k).toNat

theorem pieceWeight_apply (m : Q.ArrowEntry →₀ ℕ) (k : Fin Q.n) :
    Q.pieceWeight m k = ∑ v, (m v : ℤ) *
      ((Pi.single (Q.pos (Q.src v.1) v.2.1) (1 : ℤ) : Schubert.RS.Weight Q.n) k -
        (Pi.single (Q.pos (Q.tgt v.1) v.2.2) (1 : ℤ) : Schubert.RS.Weight Q.n) k) := by
  simp [pieceWeight, positiveRoot, Finset.sum_apply, nsmul_eq_mul]

theorem nonneg_pieceExponent {ℓ : Q.Arrow → ℕ} {m : Q.ArrowEntry →₀ ℕ} (hm : m ∈ Q.pieceSet ℓ)
    {c : Fin Q.s → ℕ} (hc : ∀ q, Q.inDegree ℓ q ≤ c q) (k : Fin Q.n) :
    0 ≤ exponentWeight (blockDetExponent Q.dim c) k + Q.pieceWeight m k := by
  set q := (finSigmaFinEquiv.symm k).1
  have hbd : exponentWeight (blockDetExponent Q.dim c) k = (c q : ℤ) := by
    simp [exponentWeight, blockDetExponent, q]
  have hterm : ∀ v : Q.ArrowEntry, -(if Q.tgt v.1 = q then (m v : ℤ) else 0) ≤
      (m v : ℤ) * ((Pi.single (Q.pos (Q.src v.1) v.2.1) (1 : ℤ) : Schubert.RS.Weight Q.n) k -
        (Pi.single (Q.pos (Q.tgt v.1) v.2.2) (1 : ℤ) : Schubert.RS.Weight Q.n) k) := by
    intro v
    have h1 : (0 : ℤ) ≤
        (Pi.single (Q.pos (Q.src v.1) v.2.1) (1 : ℤ) : Schubert.RS.Weight Q.n) k := by
      rw [Pi.single_apply]
      split_ifs <;> norm_num
    by_cases hk : k = Q.pos (Q.tgt v.1) v.2.2
    · have hq : Q.tgt v.1 = q := by
        simp [q, hk, Levi.pos]
      rw [hk] at h1
      rw [ite_eq_left hq, hk, Pi.single_eq_same]
      nlinarith [mul_nonneg ((m v).cast_nonneg (α := ℤ)) h1]
    · rw [Pi.single_eq_of_ne hk]
      have : (0 : ℤ) ≤ if Q.tgt v.1 = q then (m v : ℤ) else 0 := by split_ifs <;> simp
      nlinarith [mul_nonneg ((m v).cast_nonneg (α := ℤ)) h1]
  have hsum : -(Q.inDegree ℓ q : ℤ) ≤ Q.pieceWeight m k := by
    rw [pieceWeight_apply, inDegree, ← Q.sum_filter_arrow hm, Nat.cast_sum, Finset.sum_filter,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun v _ => ?_
    have := hterm v
    split_ifs at this ⊢ <;> simpa using this
  rw [hbd]
  have := hc q
  omega

theorem exponentWeight_pieceExponent {ℓ : Q.Arrow → ℕ} {m : Q.ArrowEntry →₀ ℕ}
    (hm : m ∈ Q.pieceSet ℓ) {c : Fin Q.s → ℕ} (hc : ∀ q, Q.inDegree ℓ q ≤ c q) :
    exponentWeight (Q.pieceExponent c m) =
      exponentWeight (blockDetExponent Q.dim c) + Q.pieceWeight m := by
  funext k
  change ((Q.pieceExponent c m k : ℕ) : ℤ) = _
  simp only [pieceExponent, Finsupp.coe_equivFunOnFinite_symm, Pi.add_apply]
  exact Int.toNat_of_nonneg (Q.nonneg_pieceExponent hm hc k)

/-- **The character of a twisted graded piece**, an ordinary polynomial: the sum over the
monomials `X^m` of multidegree `ℓ` of `x^{pieceExponent c m}`. -/
def twistedPieceCharacter (ℓ : Q.Arrow → ℕ) (c : Fin Q.s → ℕ) : Schubert.RS.Polynomial Q.n :=
  ∑ m : Q.pieceSet ℓ, monomial (Q.pieceExponent c (m : Q.ArrowEntry →₀ ℕ)) 1

/-- **As a Laurent polynomial, the character of the twisted piece is
`∏_q (∏_{i ∈ I_q} x_i)^{c_q} · ∏_e h_{ℓ_e}(x_i/x_j)`.** -/
theorem toLaurent_twistedPieceCharacter (ℓ : Q.Arrow → ℕ) (c : Fin Q.s → ℕ)
    (hc : ∀ q, Q.inDegree ℓ q ≤ c q) :
    toLaurent (Q.twistedPieceCharacter ℓ c) =
      toLaurent (blockDetMonomial Q.dim c) * Q.gradedCharacter ℓ := by
  rw [twistedPieceCharacter, map_sum, gradedCharacter_eq_sum_monomials, Finset.mul_sum,
    toLaurent_blockDetMonomial]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [toLaurent_monomial, Q.exponentWeight_pieceExponent m.2 hc,
    AddMonoidAlgebra.single_mul_single, mul_one]

/-- **`twistedPieceCharacter ℓ c` is the character of the twisted graded piece.** -/
theorem isLeviCharacter_twist_coordPiece (ℓ : Q.Arrow → ℕ) (c : Fin Q.s → ℕ)
    (hc : ∀ q, Q.inDegree ℓ q ≤ c q) :
    IsLeviCharacter (W := TensorProduct ℂ (Q.coordPiece ℓ).toSubmodule ℂ) Q.dim
      (Q.twistedPiece ℓ c) (Q.twistedPieceCharacter ℓ c) := by
  intro t
  have hchar := _root_.Representation.char_ofLinearCharacter
    (leviDetCharacter Q.dim fun q => (c q : ℤ)) (leviTorus Q.dim t)
  rw [_root_.Representation.character] at hchar
  rw [twistedPiece, leviTwist, _root_.Representation.tprod_apply, LinearMap.trace_tensorProduct',
    trace_coordPiece_leviTorus, ← laurentEval_toLaurent,
    Q.toLaurent_twistedPieceCharacter ℓ c hc, map_mul, laurentEval_toLaurent,
    eval₂_blockDetMonomial, gradedCharacter_eq_sum_monomials, map_sum, leviDetChar, hchar,
    leviDetCharacter_leviTorus]
  simp only [zpow_natCast, laurentEval_single_pieceWeight]
  ring

end

end Schubert.RS.Quiver.ForwardQuiver
