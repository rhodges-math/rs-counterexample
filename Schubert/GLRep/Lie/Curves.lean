import Schubert.GLRep.Lie.Differential
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Polynomial

/-!
# The differential along lines through the identity

For a polynomial representation `ρ` of `GL_n(K)` and a matrix `X`, the matrix `ρ(1 + tX)` is a
polynomial in `t` (`GLRep.IsPolynomialRep.curve`), defined for every `t` through the extension of
`ρ` to matrices over `K[t]`. Its constant coefficient is `1`, and its linear coefficient is the
differential `dρ(X)` (`GLRep.IsPolynomialRep.coeff_one_curve`).

For all but finitely many `t ∈ K` the matrix `1 + tX` is invertible, and there the curve is the
matrix of `ρ(1 + tX)`. So any polynomial formula for `ρ(1 + tX) w` valid at those `t` computes
`dρ(X) w` as its linear coefficient (`GLRep.IsPolynomialRep.lie_apply_eq_of_forall`). This is the
basic tool for computing the differential of concrete representations.

## Main definitions

* `GLRep.IsPolynomialRep.curve`: the polynomial matrix `ρ(1 + tX)`.
* `GLRep.lineGL`: the invertible matrix `1 + tX`, for `t` with `det(1 + tX) ≠ 0`.

## Main results

* `GLRep.IsPolynomialRep.coeff_zero_curve`, `GLRep.IsPolynomialRep.coeff_one_curve`.
* `GLRep.infinite_setOf_det_ne_zero`: `1 + tX` is invertible for infinitely many `t`.
* `GLRep.IsPolynomialRep.lie_apply_eq_of_forall`: computing `dρ(X) w` from a polynomial formula
  for `ρ(1 + tX) w`.
-/

namespace GLRep

open Module Polynomial

noncomputable section

variable {K : Type*} [Field K] {n : ℕ}
variable {W : Type*} [AddCommGroup W] [Module K W] {ρ : Representation K (GL (Fin n) K) W}

/-- The matrix `1 + tX` over the polynomial ring `K[t]`. -/
def lineMatrix (X : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K[X] :=
  1 + (Polynomial.X : K[X]) • X.map Polynomial.C

/-- The invertible matrix `1 + tX`, for `t` with `det(1 + tX) ≠ 0`. -/
def lineGL (X : Matrix (Fin n) (Fin n) K) (t : K) (ht : (1 + t • X).det ≠ 0) : GL (Fin n) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero _ ht

@[simp] theorem coe_lineGL (X : Matrix (Fin n) (Fin n) K) (t : K) (ht : (1 + t • X).det ≠ 0) :
    (lineGL X t ht : Matrix (Fin n) (Fin n) K) = 1 + t • X := rfl

theorem lineMatrix_map_aeval {B : Type*} [CommRing B] [Algebra K B] (X : Matrix (Fin n) (Fin n) K)
    (b : B) : (lineMatrix X).map (aeval b) = 1 + b • X.map (algebraMap K B) := by
  refine Matrix.ext fun i j => ?_
  simp [lineMatrix, Matrix.one_apply, apply_ite]
  exact mul_comm _ _

/-- The determinant of `1 + tX` is a polynomial in `t` with constant term `1`; so `1 + tX` is
invertible for all but finitely many `t`. -/
theorem infinite_setOf_det_ne_zero [Infinite K] (X : Matrix (Fin n) (Fin n) K) :
    {t : K | (1 + t • X).det ≠ 0}.Infinite := by
  set d : K[X] := (lineMatrix X).det
  have hd : ∀ t : K, d.eval t = (1 + t • X).det := fun t => by
    have := congrArg Matrix.det (lineMatrix_map_aeval X t)
    rw [← AlgHom.mapMatrix_apply, ← AlgHom.map_det] at this
    simpa [coe_aeval_eq_eval] using this
  have hd0 : d ≠ 0 := fun h0 => by
    have := hd 0
    rw [h0, eval_zero, zero_smul, add_zero, Matrix.det_one] at this
    exact zero_ne_one this
  have hfin := Polynomial.finite_setOfPred_isRoot hd0
  refine (Set.infinite_univ.sdiff hfin).mono fun t ht => ?_
  simp only [Set.mem_sdiff, Set.mem_univ, Set.mem_ofPred_eq, IsRoot, true_and] at ht
  simpa [hd] using ht

namespace IsPolynomialRep

variable (h : IsPolynomialRep ρ)

/-- The matrix `ρ(1 + tX)`, a matrix of polynomials in `t`. -/
def curve (X : Matrix (Fin n) (Fin n) K) : Matrix (Idx (K := K) W) (Idx (K := K) W) K[X] :=
  h.extend K[X] (lineMatrix X)

theorem curve_map_aeval {B : Type*} [CommRing B] [Algebra K B] (X : Matrix (Fin n) (Fin n) K)
    (b : B) : (h.curve X).map (aeval b) = h.extend B (1 + b • X.map (algebraMap K B)) := by
  rw [curve, ← h.extend_map, lineMatrix_map_aeval]

/-- At a point `t` where `1 + tX` is invertible, the curve is the matrix of `ρ(1 + tX)`. -/
theorem curve_map_eval (X : Matrix (Fin n) (Fin n) K) (t : K) (ht : (1 + t • X).det ≠ 0) :
    (h.curve X).map (eval t) = LinearMap.toMatrix h.basis h.basis (ρ (lineGL X t ht)) := by
  have := h.curve_map_aeval X t
  simp only [coe_aeval_eq_eval, Algebra.algebraMap_self] at this
  rw [this, ← h.extend_glCoord, coe_lineGL]
  congr 1

/-- The constant coefficient of the curve is the identity. -/
theorem coeff_zero_curve (X : Matrix (Fin n) (Fin n) K) : (h.curve X).map (coeff · 0) = 1 := by
  have := h.curve_map_aeval X (0 : K)
  rw [zero_smul, add_zero, h.extend_one] at this
  refine Matrix.ext fun i j => ?_
  have hij := congrFun (congrFun this i) j
  simp only [Matrix.map_apply, coe_aeval_eq_eval] at hij ⊢
  rw [← hij, Polynomial.coeff_zero_eq_eval_zero]

/-- The linear coefficient of a polynomial is read off at the dual number `ε`. -/
theorem snd_aeval_eps (p : K[X]) : (aeval (DualNumber.eps : DualNumber K) p).snd = p.coeff 1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial k c =>
    rcases k with _ | _ | k
    · simp [TrivSqZeroExt.algebraMap_eq_inl]
    · simp [TrivSqZeroExt.algebraMap_eq_inl]
    · simp [pow_succ, TrivSqZeroExt.algebraMap_eq_inl, coeff_monomial]

/-- **The linear coefficient of the curve is the differential.** -/
theorem coeff_one_curve (X : Matrix (Fin n) (Fin n) K) :
    (h.curve X).map (coeff · 1) = h.lieMatrix X := by
  have := h.curve_map_aeval X (DualNumber.eps : DualNumber K)
  rw [h.extend_one_add_eps] at this
  refine Matrix.ext fun i j => ?_
  have hij := congrArg TrivSqZeroExt.snd (congrFun (congrFun this i) j)
  simp only [Matrix.map_apply, snd_aeval_eps] at hij
  rw [Matrix.map_apply, hij]
  simp [Matrix.one_apply, apply_ite, TrivSqZeroExt.algebraMap_eq_inl]

/-- **Computing the differential on a vector.** If `ρ(1 + tX) w = ∑_{k < N} tᵏ vₖ` at every `t`
where `1 + tX` is invertible, and `1 < N`, then `dρ(X) w = v₁`. -/
theorem lie_apply_eq_of_forall [Infinite K] (X : Matrix (Fin n) (Fin n) K) (w : W) {N : ℕ}
    (hN : 1 < N) (v : ℕ → W)
    (hv : ∀ t (ht : (1 + t • X).det ≠ 0), ρ (lineGL X t ht) w = ∑ k ∈ Finset.range N, t ^ k • v k) :
    h.lie X w = v 1 := by
  -- the coordinates of `ρ(1 + tX) w`, as polynomials in `t`
  have := h.finiteDimensional
  set b := h.basis
  have key : ∀ i, ((h.curve X).mulVec fun j => C (b.repr w j)) i =
      ∑ k ∈ Finset.range N, monomial k (b.repr (v k) i) := by
    intro i
    refine Polynomial.eq_of_infinite_eval_eq _ _
      ((infinite_setOf_det_ne_zero X).mono fun t ht => ?_)
    have hcoord := congrArg (fun u => b.repr u i) (hv t ht)
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul] at hcoord
    rw [← LinearMap.toMatrix_mulVec_repr b b, ← h.curve_map_eval X t ht] at hcoord
    have hev : eval t (((h.curve X).mulVec fun j => C (b.repr w j)) i) =
        ((h.curve X).map (eval t)).mulVec (b.repr w) i := by
      simp [Matrix.mulVec, dotProduct, eval_finsetSum]
    simp only [Set.mem_ofPred_eq, eval_finsetSum, eval_monomial]
    rw [hev, hcoord]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  -- the linear coefficient
  apply b.repr.injective
  ext i
  have hi := congrArg (coeff · 1) (key i)
  simp only [Matrix.mulVec, dotProduct, finsetSum_coeff, coeff_mul_C, coeff_monomial,
    Finset.sum_ite_eq', Finset.mem_range, hN, ite_true] at hi
  rw [← LinearMap.toMatrix_mulVec_repr b b, h.toMatrix_lie, ← h.coeff_one_curve]
  simpa [Matrix.mulVec, dotProduct] using hi

/-- The coefficient of `tᵏ` in `ρ(1 + tX)`, as an endomorphism of `W`. -/
def curveCoeff (X : Matrix (Fin n) (Fin n) K) (k : ℕ) : Module.End K W :=
  Matrix.toLin h.basis h.basis ((h.curve X).map (coeff · k))

/-- A bound for the degree in `t` of `ρ(1 + tX)`. -/
def curveDegree (X : Matrix (Fin n) (Fin n) K) : ℕ :=
  ∑ i, ∑ j, (h.curve X i j).natDegree

theorem curveCoeff_zero (X : Matrix (Fin n) (Fin n) K) : h.curveCoeff X 0 = 1 := by
  rw [curveCoeff, h.coeff_zero_curve, Matrix.toLin_one]
  rfl

theorem curveCoeff_one [Infinite K] (X : Matrix (Fin n) (Fin n) K) :
    h.curveCoeff X 1 = h.lie X := by
  rw [curveCoeff, h.coeff_one_curve, lie_apply]

theorem natDegree_curve_le (X : Matrix (Fin n) (Fin n) K) (i j : Idx (K := K) W) :
    (h.curve X i j).natDegree ≤ h.curveDegree X :=
  (Finset.single_le_sum (f := fun j => (h.curve X i j).natDegree) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ j)).trans (Finset.single_le_sum
      (f := fun i => ∑ j, (h.curve X i j).natDegree) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i))

theorem curveCoeff_eq_zero (X : Matrix (Fin n) (Fin n) K) {k : ℕ} (hk : h.curveDegree X < k) :
    h.curveCoeff X k = 0 := by
  have hz : (h.curve X).map (coeff · k) = 0 := Matrix.ext fun i j =>
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (h.natDegree_curve_le X i j) hk)
  rw [curveCoeff, hz, map_zero]

/-- **`ρ(1 + tX)` as a polynomial in `t`**, at every `t` where `1 + tX` is invertible. -/
theorem rho_lineGL_eq_sum (X : Matrix (Fin n) (Fin n) K) (t : K) (ht : (1 + t • X).det ≠ 0)
    {N : ℕ} (hN : h.curveDegree X < N) :
    ρ (lineGL X t ht) = ∑ k ∈ Finset.range N, t ^ k • h.curveCoeff X k := by
  have hmat : LinearMap.toMatrix h.basis h.basis (ρ (lineGL X t ht)) =
      ∑ k ∈ Finset.range N, t ^ k • (h.curve X).map (coeff · k) := by
    rw [← h.curve_map_eval X t ht]
    refine Matrix.ext fun i j => ?_
    rw [Matrix.map_apply, Matrix.sum_apply,
      eval_eq_sum_range' (lt_of_le_of_lt (h.natDegree_curve_le X i j) hN)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, mul_comm]
  rw [← (LinearMap.toMatrix h.basis h.basis).symm_apply_apply (ρ _), hmat,
    LinearMap.toMatrix_symm, map_sum]
  simp only [map_smul, curveCoeff]

end IsPolynomialRep

end

end GLRep
