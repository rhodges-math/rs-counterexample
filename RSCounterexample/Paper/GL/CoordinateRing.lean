import RSCounterexample.Paper.GL.Twist
import RSCounterexample.Paper.Quiver.Multiplicity
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Matrix.Block

/-!
# The coordinate ring of a quiver representation space

For a forward quiver `Q` with vertex spaces `V_p = ℂ^{dim p}`, the representation space is
`Rep_Q = ⊕_{e : p → q} Hom(V_p, V_q)`, on which `L = ∏_p GL(V_p)` acts by
`g · (X_e)_e = (g_q X_e g_p⁻¹)_e`. Its coordinate ring `R_Q` is the polynomial ring in the matrix
entries of the `X_e`, with the contragredient action `(g · f)(X) = f(g⁻¹ · X)`.

The coordinate `X ⟨e, (i, j)⟩` is the entry `(j, i)` of `X_e`: `i` indexes the basis of the source
`V_p` and `j` that of the target `V_q`. Under the contragredient action
`X_e ↦ g_q⁻¹ X_e g_p`, so `g` sends `X ⟨e, (i, j)⟩` to `∑_{i', j'} (g_p)_{i' i} (g_q⁻¹)_{j j'}
X ⟨e, (i', j')⟩`, and the diagonal torus scales it by `x_i / x_j` (`Quiver.arrowMonomial`).

Grading by the number of variables of each arrow, the graded piece of multidegree `ℓ` is a
finite-dimensional subrepresentation, `⊗_e Sym^{ℓ_e}(V_p ⊗ V_q^*)`.

## Main definitions

* `Schubert.RS.Quiver.ForwardQuiver.linearSubst`: the substitution `X_v ↦ ∑_w M_{wv} X_w`.
* `Schubert.RS.Quiver.ForwardQuiver.coordRing`: `R_Q`.
* `Schubert.RS.Quiver.ForwardQuiver.coordMatrix`: the matrix of `g` on the linear coordinates.
* `Schubert.RS.Quiver.ForwardQuiver.coordRep`: the representation of `L` on `R_Q`.
* `Schubert.RS.Quiver.ForwardQuiver.arrowGrading`, `pieceSet`: the arrow multidegree.
* `Schubert.RS.Quiver.ForwardQuiver.coordPiece`: the graded piece of multidegree `ℓ`.
* `Schubert.RS.Quiver.ForwardQuiver.pieceBasis`: its monomial basis.
* `Schubert.RS.Quiver.ForwardQuiver.inDegree`, `outDegree`: `∑_{e : · → q} ℓ_e` and
  `∑_{e : p → ·} ℓ_e`.
-/

namespace Schubert.RS.Quiver.ForwardQuiver

noncomputable section

open Matrix MvPolynomial
open scoped Kronecker

/-! ### Linear substitutions -/

section LinearSubst

variable {σ : Type*} [Fintype σ]

/-- The linear substitution `X_v ↦ ∑_w M_{wv} X_w`. -/
def linearSubst (M : Matrix σ σ ℂ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  aeval fun v => ∑ w, M w v • X w

@[simp]
theorem linearSubst_X (M : Matrix σ σ ℂ) (v : σ) : linearSubst M (X v) = ∑ w, M w v • X w :=
  aeval_X _ _

variable [DecidableEq σ] in
theorem linearSubst_one : linearSubst (1 : Matrix σ σ ℂ) = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [Matrix.one_apply]

theorem linearSubst_mul (M N : Matrix σ σ ℂ) :
    linearSubst (M * N) = (linearSubst M).comp (linearSubst N) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [linearSubst_X, AlgHom.comp_apply, map_sum, map_smul, Matrix.mul_apply,
    Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun u _ => ?_
  rw [mul_comm]

variable [DecidableEq σ] in
/-- A diagonal substitution scales each monomial. -/
theorem linearSubst_diagonal_monomial (δ : σ → ℂ) (m : σ →₀ ℕ) (a : ℂ) :
    linearSubst (Matrix.diagonal δ) (monomial m a) = (∏ v, δ v ^ m v) • monomial m a := by
  have h : linearSubst (Matrix.diagonal δ) = aeval fun v => C (δ v) * X v := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [Matrix.diagonal_apply, ite_smul, smul_eq_C_mul]
  rw [h, aeval_monomial, monomial_eq, smul_eq_C_mul, algebraMap_eq,
    Finsupp.prod_fintype _ _ fun _ => pow_zero _, Finsupp.prod_fintype _ _ fun _ => pow_zero _]
  simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
  ring

omit [Fintype σ] in
/-- If every substituted value is weighted homogeneous of the weight of its variable, the
substitution preserves weighted homogeneity. -/
theorem isWeightedHomogeneous_aeval {M : Type*} [AddCommMonoid M] {w : σ → M}
    {φ : MvPolynomial σ ℂ} {m : M} (hφ : φ.IsWeightedHomogeneous w m)
    (f : σ → MvPolynomial σ ℂ) (hf : ∀ v, (f v).IsWeightedHomogeneous w (w v)) :
    (aeval f φ).IsWeightedHomogeneous w m := by
  classical
  rw [φ.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  have hd' : Finsupp.weight w d = m := hφ (mem_support_iff.mp hd)
  rw [aeval_monomial, ← hd', Finsupp.weight_apply, algebraMap_eq]
  exact IsWeightedHomogeneous.C_mul
    (IsWeightedHomogeneous.prod _ _ _ fun i _ => (hf i).pow _) _

end LinearSubst

variable (Q : ForwardQuiver)

/-! ### The coordinate ring and the action -/

/-- The coordinates of `Rep_Q = ⊕_{e : p → q} Hom(V_p, V_q)`: `⟨e, (i, j)⟩` is the entry `(j, i)`
of `X_e`, with `i` a basis index of `V_p` and `j` one of `V_q`. -/
abbrev ArrowEntry : Type := Σ e : Q.Arrow, Fin (Q.dim (Q.src e)) × Fin (Q.dim (Q.tgt e))

/-- **The coordinate ring `R_Q`** of the representation space of `Q`. -/
abbrev coordRing : Type := MvPolynomial Q.ArrowEntry ℂ

/-- The matrix of `g ∈ L` on the linear coordinates of `Rep_Q`: on the coordinates of the arrow
`e : p → q` it is `g_p ⊗ (g_q⁻¹)ᵀ`. -/
def coordMatrix : GL.LeviGroup Q.dim →* Matrix Q.ArrowEntry Q.ArrowEntry ℂ where
  toFun g := blockDiagonal' fun e =>
    (g (Q.src e) : Matrix _ _ ℂ) ⊗ₖ (((g (Q.tgt e))⁻¹ : GL _ ℂ) : Matrix _ _ ℂ)ᵀ
  map_one' := by
    simp only [Pi.one_apply, Units.val_one, inv_one, transpose_one, one_kronecker_one]
    exact blockDiagonal'_one
  map_mul' g h := by
    simp only [Pi.mul_apply, _root_.mul_inv_rev, Units.val_mul, transpose_mul,
      mul_kronecker_mul]
    exact blockDiagonal'_mul _ _

theorem coordMatrix_apply (g : GL.LeviGroup Q.dim) :
    Q.coordMatrix g = blockDiagonal' fun e =>
      (g (Q.src e) : Matrix _ _ ℂ) ⊗ₖ (((g (Q.tgt e))⁻¹ : GL _ ℂ) : Matrix _ _ ℂ)ᵀ :=
  rfl

theorem coordMatrix_apply_same (g : GL.LeviGroup Q.dim) (e : Q.Arrow)
    (a b : Fin (Q.dim (Q.src e)) × Fin (Q.dim (Q.tgt e))) :
    Q.coordMatrix g ⟨e, a⟩ ⟨e, b⟩ =
      (g (Q.src e) : Matrix _ _ ℂ) a.1 b.1 *
        (((g (Q.tgt e))⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) b.2 a.2 := by
  rw [coordMatrix_apply, blockDiagonal'_apply_eq, kroneckerMap_apply, transpose_apply]

theorem coordMatrix_apply_ne (g : GL.LeviGroup Q.dim) {u v : Q.ArrowEntry} (h : u.1 ≠ v.1) :
    Q.coordMatrix g u v = 0 := by
  obtain ⟨e, a⟩ := u
  obtain ⟨e', b⟩ := v
  rw [coordMatrix_apply]
  exact blockDiagonal'_apply_ne _ _ _ h

/-- **The representation of `L` on `R_Q`**: `(g · f)(X) = f(g⁻¹ · X)`, the linear substitution by
`coordMatrix g`. -/
def coordRep : _root_.Representation ℂ (GL.LeviGroup Q.dim) Q.coordRing where
  toFun g := (linearSubst (Q.coordMatrix g)).toLinearMap
  map_one' := by rw [map_one, linearSubst_one]; rfl
  map_mul' g h := by rw [map_mul, linearSubst_mul]; rfl

theorem coordRep_apply (g : GL.LeviGroup Q.dim) (φ : Q.coordRing) :
    Q.coordRep g φ = linearSubst (Q.coordMatrix g) φ :=
  rfl

/-- **The action on the coordinates:** `g · X ⟨e, (i, j)⟩ = ∑_{i', j'} (g_p)_{i' i} (g_q⁻¹)_{j j'}
X ⟨e, (i', j')⟩`, i.e. `X_e ↦ g_q⁻¹ X_e g_p`. -/
theorem coordRep_X (g : GL.LeviGroup Q.dim) (v : Q.ArrowEntry) :
    Q.coordRep g (X v) =
      ∑ i', ∑ j', ((g (Q.src v.1) : Matrix _ _ ℂ) i' v.2.1 *
        (((g (Q.tgt v.1))⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) v.2.2 j') • X ⟨v.1, (i', j')⟩ := by
  obtain ⟨e, a⟩ := v
  rw [coordRep_apply, linearSubst_X, Fintype.sum_sigma, Finset.sum_eq_single e]
  · rw [Fintype.sum_prod_type]
    simp only [coordMatrix_apply_same]
  · intro e' _ he'
    exact Finset.sum_eq_zero fun b _ => by
      rw [Q.coordMatrix_apply_ne g (u := ⟨e', b⟩) (v := ⟨e, a⟩) he', zero_smul]
  · simp

/-- The torus weight of the coordinate `X ⟨e, (i, j)⟩`: `t_i / t_j`, with `i` in the block of the
source and `j` in the block of the target. -/
def entryWeight (t : Fin Q.n → ℂˣ) (v : Q.ArrowEntry) : ℂ :=
  (t (Q.pos (Q.src v.1) v.2.1) : ℂ) * ((t (Q.pos (Q.tgt v.1) v.2.2))⁻¹ : ℂˣ)

theorem coordMatrix_leviTorus (t : Fin Q.n → ℂˣ) :
    Q.coordMatrix (GL.leviTorus Q.dim t) = Matrix.diagonal (Q.entryWeight t) := by
  have hinv : ∀ q : Fin Q.s, (((GL.leviTorus Q.dim t q)⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) =
      Matrix.diagonal fun j => (((t (Q.pos q j))⁻¹ : ℂˣ) : ℂ) := by
    intro q
    rw [GL.leviTorus, ← map_inv, TauCeti.diagGL_coe]
    rfl
  rw [coordMatrix_apply]
  simp only [hinv]
  simp only [GL.leviTorus, TauCeti.diagGL_coe, diagonal_transpose,
    diagonal_kronecker_diagonal, blockDiagonal'_diagonal]
  rfl

/-- **The diagonal torus acts on monomials by their weights.** -/
theorem coordRep_leviTorus_monomial (t : Fin Q.n → ℂˣ) (m : Q.ArrowEntry →₀ ℕ) (a : ℂ) :
    Q.coordRep (GL.leviTorus Q.dim t) (monomial m a) =
      (∏ v, Q.entryWeight t v ^ m v) • monomial m a := by
  rw [coordRep_apply, coordMatrix_leviTorus, linearSubst_diagonal_monomial]

/-! ### The arrow grading -/

/-- The arrow grading: the coordinate `⟨e, (i, j)⟩` has multidegree the indicator of `e`. -/
def arrowGrading (v : Q.ArrowEntry) : Q.Arrow → ℕ := Pi.single v.1 1

theorem weight_arrowGrading_apply (m : Q.ArrowEntry →₀ ℕ) (e : Q.Arrow) :
    Finsupp.weight Q.arrowGrading m e = ∑ a, m ⟨e, a⟩ := by
  rw [Finsupp.weight_eq_sum, Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single e]
  · simp [arrowGrading]
  · intro e' _ he'
    exact Finset.sum_eq_zero fun b _ => by simp [arrowGrading, he'.symm]
  · simp

/-- The exponents of arrow multidegree `ℓ`. -/
def pieceSet (ℓ : Q.Arrow → ℕ) : Set (Q.ArrowEntry →₀ ℕ) :=
  {m | Finsupp.weight Q.arrowGrading m = ℓ}

theorem pieceSet_finite (ℓ : Q.Arrow → ℕ) : (Q.pieceSet ℓ).Finite := by
  refine (Finsupp.finite_of_degree_eq (σ := Q.ArrowEntry) (∑ e, ℓ e)).subset fun m hm => ?_
  simp only [pieceSet, Set.mem_ofPred_eq] at hm ⊢
  rw [Finsupp.degree_eq_sum, ← hm, Fintype.sum_sigma]
  simp only [weight_arrowGrading_apply]

noncomputable instance (ℓ : Q.Arrow → ℕ) : Fintype (Q.pieceSet ℓ) :=
  (Q.pieceSet_finite ℓ).fintype

/-- The coordinate substitution of `g` preserves the arrow grading. -/
theorem isWeightedHomogeneous_coordRep (g : GL.LeviGroup Q.dim) {φ : Q.coordRing}
    {ℓ : Q.Arrow → ℕ} (hφ : φ.IsWeightedHomogeneous Q.arrowGrading ℓ) :
    (Q.coordRep g φ).IsWeightedHomogeneous Q.arrowGrading ℓ := by
  refine isWeightedHomogeneous_aeval hφ _ fun v => IsWeightedHomogeneous.sum _ _ _ fun u _ => ?_
  by_cases h : u.1 = v.1
  · have hu : Q.arrowGrading u = Q.arrowGrading v := by simp [arrowGrading, h]
    rw [← hu]
    exact (weightedHomogeneousSubmodule ℂ Q.arrowGrading _).smul_mem _
      (isWeightedHomogeneous_X ℂ _ u)
  · rw [Q.coordMatrix_apply_ne g h, zero_smul]
    exact isWeightedHomogeneous_zero ℂ _ _

/-- **The graded piece of `R_Q` of arrow multidegree `ℓ`**, `⊗_e Sym^{ℓ_e}(V_p ⊗ V_q^*)`: the
polynomials with `ℓ_e` variables of each arrow `e` in every monomial. -/
def coordPiece (ℓ : Q.Arrow → ℕ) : Subrepresentation Q.coordRep where
  toSubmodule := weightedHomogeneousSubmodule ℂ Q.arrowGrading ℓ
  apply_mem_toSubmodule g _ hφ := Q.isWeightedHomogeneous_coordRep g hφ

theorem mem_pieceSet {ℓ : Q.Arrow → ℕ} {m : Q.ArrowEntry →₀ ℕ} :
    m ∈ Q.pieceSet ℓ ↔ Finsupp.weight Q.arrowGrading m = ℓ :=
  Iff.rfl

theorem mem_coordPiece (ℓ : Q.Arrow → ℕ) (φ : Q.coordRing) :
    φ ∈ (Q.coordPiece ℓ).toSubmodule ↔ φ.IsWeightedHomogeneous Q.arrowGrading ℓ :=
  Iff.rfl

theorem coordPiece_toSubmodule (ℓ : Q.Arrow → ℕ) :
    (Q.coordPiece ℓ).toSubmodule = restrictSupport ℂ (Q.pieceSet ℓ) :=
  weightedHomogeneousSubmodule_eq_finsupp_supported ℂ Q.arrowGrading ℓ

/-- **The monomial basis of a graded piece**, indexed by the exponents of multidegree `ℓ`. -/
def pieceBasis (ℓ : Q.Arrow → ℕ) :
    Module.Basis (Q.pieceSet ℓ) ℂ (Q.coordPiece ℓ).toSubmodule :=
  (basisRestrictSupport ℂ (Q.pieceSet ℓ)).map
    (LinearEquiv.ofEq _ _ (Q.coordPiece_toSubmodule ℓ).symm)

theorem pieceBasis_repr (ℓ : Q.Arrow → ℕ) (φ : (Q.coordPiece ℓ).toSubmodule)
    (m : Q.pieceSet ℓ) :
    (Q.pieceBasis ℓ).repr φ m = (φ : Q.coordRing).coeff (m : Q.ArrowEntry →₀ ℕ) :=
  rfl

theorem pieceBasis_apply (ℓ : Q.Arrow → ℕ) (m : Q.pieceSet ℓ) :
    ((Q.pieceBasis ℓ m : (Q.coordPiece ℓ).toSubmodule) : Q.coordRing) =
      monomial (m : Q.ArrowEntry →₀ ℕ) 1 := by
  have hmem : monomial (m : Q.ArrowEntry →₀ ℕ) (1 : ℂ) ∈ (Q.coordPiece ℓ).toSubmodule := by
    rw [coordPiece_toSubmodule, monomial_mem_restrictSupport]
    exact Or.inl m.2
  have h : Q.pieceBasis ℓ m = ⟨_, hmem⟩ := by
    apply (Q.pieceBasis ℓ).repr.injective
    rw [Module.Basis.repr_self]
    ext m'
    rw [pieceBasis_repr, coeff_monomial, Finsupp.single_apply]
    exact if_congr Subtype.ext_iff rfl rfl
  rw [h]

instance (ℓ : Q.Arrow → ℕ) : FiniteDimensional ℂ (Q.coordPiece ℓ).toSubmodule :=
  Module.Finite.of_basis (Q.pieceBasis ℓ)

/-- The matrix coefficients of a graded piece in the monomial basis. -/
theorem toMatrix_pieceBasis (ℓ : Q.Arrow → ℕ) [DecidableEq (Q.pieceSet ℓ)] (g : GL.LeviGroup Q.dim)
    (m m' : Q.pieceSet ℓ) :
    LinearMap.toMatrix (Q.pieceBasis ℓ) (Q.pieceBasis ℓ) ((Q.coordPiece ℓ).toRepresentation g)
        m' m =
      (Q.coordRep g (monomial (m : Q.ArrowEntry →₀ ℕ) 1)).coeff (m' : Q.ArrowEntry →₀ ℕ) := by
  rw [LinearMap.toMatrix_apply, pieceBasis_repr, ← pieceBasis_apply]
  rfl

/-- **The trace of a torus element on a graded piece:** the sum of the weights of the monomials
of multidegree `ℓ`. -/
theorem trace_coordPiece_leviTorus (ℓ : Q.Arrow → ℕ) (t : Fin Q.n → ℂˣ) :
    LinearMap.trace ℂ _ ((Q.coordPiece ℓ).toRepresentation (GL.leviTorus Q.dim t)) =
      ∑ m : Q.pieceSet ℓ, ∏ v, Q.entryWeight t v ^ (m : Q.ArrowEntry →₀ ℕ) v := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (Q.pieceBasis ℓ), Matrix.trace]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Matrix.diag_apply, toMatrix_pieceBasis, coordRep_leviTorus_monomial, coeff_smul,
    coeff_monomial]
  simp

/-! ### In- and out-degrees -/

/-- The in-degree `∑_{e : · → q} ℓ_e` of a vertex. -/
def inDegree (ℓ : Q.Arrow → ℕ) (q : Fin Q.s) : ℕ :=
  ∑ e ∈ Finset.univ.filter (fun e => Q.tgt e = q), ℓ e

/-- The out-degree `∑_{e : p → ·} ℓ_e` of a vertex. -/
def outDegree (ℓ : Q.Arrow → ℕ) (p : Fin Q.s) : ℕ :=
  ∑ e ∈ Finset.univ.filter (fun e => Q.src e = p), ℓ e

end

end Schubert.RS.Quiver.ForwardQuiver
