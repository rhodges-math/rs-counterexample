import Schubert.FlagVarieties.Schubert.ParabolicSemiInvariants
import Schubert.FlagVarieties.Schubert.SimpleSchubertIso

/-!
# `H⁰(X_{sᵢ}, 𝓛(η))`

Let `i + 1 < n`, `η ∈ ℤⁿ` and `d = η_{i+1} - ηᵢ = -⟨η, αᵢ^∨⟩` (so `d ≥ 0` for `η` weakly increasing,
the antidominant weights). Over every commutative ring `R`:

* `FlagVarieties.simpleSchubertSectionsEquiv`: `H⁰(X_{sᵢ}, 𝓛(η)) ≅ R[τ]_{< d + 1}`, the polynomials
  of degree `≤ d` (zero if `d < 0`), by `f ↦ f(1 + τ E_{i+1,i})` (`FlagVarieties.lowerEval`).
  So `H⁰(X_{sᵢ}, 𝓛(η))` is free of rank `max(0, d + 1)`
  (`FlagVarieties.finrank_sections_simpleSchubert`).
* `FlagVarieties.simpleSemiInvariant R i hi η k` (`k ≤ d`): the section corresponding to `τᵏ`,
  `U · pᵢᵢ^{d-k} p_{i+1,i}^k` with `U` a unit
  (`FlagVarieties.lowerEval_simpleSemiInvariant`). In the coordinates `[pᵢᵢ : p_{i+1,i}]` of
  `X_{sᵢ} ≅ ℙ¹` (`FlagVarieties.simpleSchubertIsoLine`), these are the binary forms of degree `d`,
  matching `𝓛(η)|_{X_{sᵢ}} ≅ 𝒪(d)`. The sheaf-level isomorphism with `𝒪(d)` is not formalized here:
  `𝒪(d)` on `ℙ¹` is not defined in this library or in Mathlib.

The proof restricts a semi-invariant `f` to the two lines `1 + τ E_{i+1,i}` and
`(1 + σ E_{i,i+1}) sᵢ` of `Pᵢ` (polynomials `φ(τ)`, `ψ(σ)`). Over `R[T, T⁻¹]` these lines differ by
an element of `B`, so `ψ(T) = ± T^d φ(T⁻¹)`, forcing `deg φ ≤ d`
(`FlagVarieties.lowerEval_mem_degreeLT`). Over the open sets `pᵢᵢ ≠ 0`, `p_{i+1,i} ≠ 0` of `Pᵢ`,
`f` is determined by `φ` and `ψ`, which gives injectivity
(`FlagVarieties.eq_zero_of_lowerEval_eq_zero`).
-/

noncomputable section

namespace FlagVarieties

open Polynomial LaurentPolynomial
open scoped TensorProduct

universe u

/-! ### Two lines in `Pᵢ` -/

section Matrices

variable {n : ℕ} (i : ℕ) (hi : i + 1 < n) {A : Type*} [CommRing A]

/-- The point `1 + x E_{i+1,i}` of `Pᵢ`. -/
abbrev lowerLineMatrix (x : A) : Matrix (Fin n) (Fin n) A :=
  Matrix.transvection (rowB n i hi) (rowA n i hi) x

/-- The point `(1 + y E_{i,i+1}) sᵢ` of `Pᵢ`. -/
abbrev upperLineMatrix (y : A) : Matrix (Fin n) (Fin n) A :=
  Matrix.transvection (rowA n i hi) (rowB n i hi) y * permMatrix n (simpleReflection n i hi)

theorem det_lowerLineMatrix (x : A) : (lowerLineMatrix i hi x).det = 1 :=
  Matrix.det_transvection_of_ne _ _ (rowA_ne_rowB n i hi).symm _

theorem isUnit_det_lowerLineMatrix (x : A) : IsUnit (lowerLineMatrix i hi x).det := by
  rw [det_lowerLineMatrix]
  exact isUnit_one

theorem isUnit_det_upperLineMatrix (y : A) : IsUnit (upperLineMatrix i hi y).det := by
  rw [Matrix.det_mul, Matrix.det_transvection_of_ne _ _ (rowA_ne_rowB n i hi), one_mul]
  exact isUnit_det_permMatrix n _

theorem lowerLineMatrix_blockTriangular (x : A) :
    (lowerLineMatrix i hi x).BlockTriangular (parabolicBlock n i) := by
  intro r c h
  rw [parabolicBlock_lt_iff] at h
  have hrc : r ≠ c := fun e => by rw [e] at h; exact lt_irrefl _ h.1
  simp only [lowerLineMatrix, Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne hrc,
    zero_add, Matrix.single_apply]
  split_ifs with h'
  · obtain ⟨rfl, rfl⟩ := h'
    exact absurd ⟨rfl, rfl⟩ h.2
  · rfl

theorem upperLineMatrix_blockTriangular (y : A) :
    (upperLineMatrix i hi y).BlockTriangular (parabolicBlock n i) :=
  Matrix.BlockTriangular.mul (blockTriangular_parabolicBlock_of_upper i
    (transvection_blockTriangular (rowA_lt_rowB n i hi) _))
    (blockTriangular_permMatrix_simpleReflection i hi)

theorem lowerLineMatrix_apply_self (x : A) (k : Fin n) : lowerLineMatrix i hi x k k = 1 := by
  have h : ¬(rowB n i hi = k ∧ rowA n i hi = k) := fun h => rowA_ne_rowB n i hi (h.2.trans h.1.symm)
  simp only [lowerLineMatrix, Matrix.transvection, Matrix.add_apply, Matrix.one_apply_eq,
    Matrix.single_apply, h, ite_false, add_zero]

theorem lowerLineMatrix_apply_BA (x : A) :
    lowerLineMatrix i hi x (rowB n i hi) (rowA n i hi) = x := by
  simp only [lowerLineMatrix, Matrix.transvection, Matrix.add_apply,
    Matrix.one_apply_ne (rowA_ne_rowB n i hi).symm, Matrix.single_apply, and_self, ite_true,
    zero_add]

theorem lowerLineMatrix_apply_AB (x : A) :
    lowerLineMatrix i hi x (rowA n i hi) (rowB n i hi) = 0 := by
  have h : ¬(rowB n i hi = rowA n i hi ∧ rowA n i hi = rowB n i hi) :=
    fun h => rowA_ne_rowB n i hi h.2
  simp only [lowerLineMatrix, Matrix.transvection, Matrix.add_apply,
    Matrix.one_apply_ne (rowA_ne_rowB n i hi), Matrix.single_apply, h, ite_false, add_zero]

theorem upperLineMatrix_inv (y : A) :
    (upperLineMatrix i hi y)⁻¹ = permMatrix n (simpleReflection n i hi) *
      Matrix.transvection (rowA n i hi) (rowB n i hi) (-y) := by
  have hw : (permMatrix (A := A) n (simpleReflection n i hi))⁻¹ =
      permMatrix n (simpleReflection n i hi) :=
    Matrix.inv_eq_left_inv (permMatrix_simpleReflection_mul_self n i hi)
  rw [upperLineMatrix, Matrix.mul_inv_rev, hw, transvection_inv (rowA_ne_rowB n i hi)]

/-- The diagonal of `((1 + σ E_{i,i+1}) sᵢ)⁻¹ (1 + τ E_{i+1,i})`. -/
theorem upperLineMatrix_inv_mul_lowerLineMatrix_apply_self (σ τ : A) (k : Fin n) :
    ((upperLineMatrix i hi σ)⁻¹ * lowerLineMatrix i hi τ) k k =
      if k = rowA n i hi then τ else if k = rowB n i hi then -σ else 1 := by
  rw [upperLineMatrix_inv, Matrix.mul_assoc, permMatrix_mul_apply, transvection_mul_apply]
  have hsymm : (simpleReflection n i hi).symm = simpleReflection n i hi := Equiv.symm_swap _ _
  rw [hsymm]
  by_cases hA : k = rowA n i hi
  · rw [hA, simpleReflection, Equiv.swap_apply_left,
      ite_eq_right_of_eq_false _ _ (eq_false (rowA_ne_rowB n i hi).symm), add_zero,
      ite_eq_left_of_eq_true _ _ (eq_self _), lowerLineMatrix_apply_BA]
  · by_cases hB : k = rowB n i hi
    · rw [hB, simpleReflection, Equiv.swap_apply_right, ite_eq_left_of_eq_true _ _ (eq_self _),
        lowerLineMatrix_apply_AB, lowerLineMatrix_apply_self, zero_add, mul_one,
        ite_eq_right_of_eq_false _ _ (eq_false (rowA_ne_rowB n i hi).symm),
        ite_eq_left_of_eq_true _ _ (eq_self _)]
    · rw [simpleReflection, Equiv.swap_apply_of_ne_of_ne hA hB,
        ite_eq_right_of_eq_false _ _ (eq_false hA), add_zero, lowerLineMatrix_apply_self,
        ite_eq_right_of_eq_false _ _ (eq_false hA), ite_eq_right_of_eq_false _ _ (eq_false hB)]

end Matrices

/-! ### Restriction of functions on `Pᵢ` to the two lines -/

variable (R : Type u) [CommRing R] {n : ℕ} (i : ℕ) (hi : i + 1 < n)

/-- **`f ↦ f(1 + τ E_{i+1,i})`**, `𝒪(Pᵢ) → R[τ]`. -/
def lowerEval : ParabolicCoord R n i →ₐ[R] R[X] :=
  parabolicPointOfMatrix i (lowerLineMatrix i hi (X : R[X])) (isUnit_det_lowerLineMatrix i hi _)
    (lowerLineMatrix_blockTriangular i hi _)

/-- **`f ↦ f((1 + σ E_{i,i+1}) sᵢ)`**, `𝒪(Pᵢ) → R[σ]`. -/
def upperEval : ParabolicCoord R n i →ₐ[R] R[X] :=
  parabolicPointOfMatrix i (upperLineMatrix i hi (X : R[X])) (isUnit_det_upperLineMatrix i hi _)
    (upperLineMatrix_blockTriangular i hi _)

variable {R}

theorem parabolicPointOfMatrix_congr {A : Type*} [CommRing A] [Algebra R A]
    {g g' : Matrix (Fin n) (Fin n) A} (h : g = g') (hg : IsUnit g.det)
    (hgb : g.BlockTriangular (parabolicBlock n i)) (hg' : IsUnit g'.det)
    (hgb' : g'.BlockTriangular (parabolicBlock n i)) :
    parabolicPointOfMatrix (R := R) i g hg hgb = parabolicPointOfMatrix i g' hg' hgb' := by
  subst h
  rfl

theorem comp_lowerEval {A : Type*} [CommRing A] [Algebra R A] (φ : R[X] →ₐ[R] A) :
    φ.comp (lowerEval R i hi) = parabolicPointOfMatrix i (lowerLineMatrix i hi (φ X))
      (isUnit_det_lowerLineMatrix i hi _) (lowerLineMatrix_blockTriangular i hi _) := by
  apply parabolicMatrix_algHom_ext
  rw [AlgHom.coe_comp, ← Matrix.map_map, lowerEval, parabolicMatrix_map_parabolicPointOfMatrix,
    parabolicMatrix_map_parabolicPointOfMatrix]
  exact map_transvection n φ.toRingHom _ _ _

theorem comp_upperEval {A : Type*} [CommRing A] [Algebra R A] (φ : R[X] →ₐ[R] A) :
    φ.comp (upperEval R i hi) = parabolicPointOfMatrix i (upperLineMatrix i hi (φ X))
      (isUnit_det_upperLineMatrix i hi _) (upperLineMatrix_blockTriangular i hi _) := by
  apply parabolicMatrix_algHom_ext
  rw [AlgHom.coe_comp, ← Matrix.map_map, upperEval, parabolicMatrix_map_parabolicPointOfMatrix,
    parabolicMatrix_map_parabolicPointOfMatrix, upperLineMatrix, upperLineMatrix, map_mul_algHom,
    show (Matrix.transvection (rowA n i hi) (rowB n i hi) (X : R[X])).map φ =
      Matrix.transvection (rowA n i hi) (rowB n i hi) (φ X) from
      map_transvection n φ.toRingHom _ _ _,
    show (permMatrix n (simpleReflection n i hi)).map φ = permMatrix n (simpleReflection n i hi)
      from permMatrix_map (v := simpleReflection n i hi) φ]

theorem lowerEval_parabolicMatrix (r c : Fin n) :
    lowerEval R i hi (parabolicMatrix R n i r c) = lowerLineMatrix i hi (X : R[X]) r c :=
  congrFun (congrFun (parabolicMatrix_map_parabolicPointOfMatrix (R := R) i
    (lowerLineMatrix i hi (X : R[X])) (isUnit_det_lowerLineMatrix i hi _)
    (lowerLineMatrix_blockTriangular i hi _)) r) c

/-! ### The comparison over `R[T, T⁻¹]` -/

/-- The unit `T` of `R[T, T⁻¹]`. -/
abbrev laurentT : R[T;T⁻¹]ˣ := (isUnit_T 1).unit

theorem val_laurentT_inv : ((laurentT⁻¹ : R[T;T⁻¹]ˣ) : R[T;T⁻¹]) = T (-1) := by
  refine (left_inv_eq_right_inv (a := ((laurentT : R[T;T⁻¹]ˣ) : R[T;T⁻¹])) ?_ ?_).symm
  · rw [IsUnit.unit_spec, ← T_add, neg_add_cancel, T_zero]
  · exact Units.mul_inv _

theorem val_laurentT_zpow (m : ℤ) : ((laurentT ^ m : R[T;T⁻¹]ˣ) : R[T;T⁻¹]) = T m := by
  induction m using Int.induction_on with
  | zero => rw [zpow_zero, Units.val_one, T_zero]
  | succ m ih => rw [zpow_add_one, Units.val_mul, ih, IsUnit.unit_spec, ← T_add]
  | pred m ih => rw [zpow_sub_one, Units.val_mul, ih, val_laurentT_inv, ← T_add, sub_eq_add_neg]

theorem val_neg_one_zpow (m : ℤ) : (((-1 : R[T;T⁻¹]ˣ) ^ m : R[T;T⁻¹]ˣ) : R[T;T⁻¹]) =
    toLaurent (((-1 : R[X]ˣ) ^ m : R[X]ˣ) : R[X]) := by
  have h : Units.map (toLaurent (R := R)).toMonoidHom (-1) = -1 :=
    Units.ext (by simp)
  rw [← h, ← map_zpow]
  rfl

theorem mul_eq_of_units {L : Type*} [CommRing L] {Ψ S S' W W' D : L} (hW : W' * W = 1)
    (hprod : W = S * D) (hS : S * S' = 1) : Ψ * S' = Ψ * W' * D := by
  linear_combination (-(Ψ * S')) * hW + (Ψ * W' * S') * hprod + (Ψ * W' * D) * hS

variable {η : Fin n → ℤ} {f : ParabolicCoord R n i}

/-- **The two restrictions of a semi-invariant**: `ψ(T) · (±1) = T^d φ(T⁻¹)` with
`d = η_{i+1} - ηᵢ`, `φ = lowerEval f`, `ψ = upperEval f`. -/
theorem toLaurent_upperEval (hf : IsParabolicSemiInvariant η f) :
    toLaurent (upperEval R i hi f * ((((-1 : R[X]ˣ) ^ η (rowB n i hi))⁻¹ : R[X]ˣ) : R[X])) =
      invert (toLaurent (lowerEval R i hi f)) * T (η (rowB n i hi) - η (rowA n i hi)) := by
  have hG₂ := isUnit_det_upperLineMatrix i hi (T 1 : R[T;T⁻¹])
  have hG₁ := isUnit_det_lowerLineMatrix i hi (T (-1) : R[T;T⁻¹])
  have hG₁b := lowerLineMatrix_blockTriangular i hi (T (-1) : R[T;T⁻¹])
  have hσ : (T 1 : R[T;T⁻¹]) *
      lowerLineMatrix i hi (T (-1) : R[T;T⁻¹]) (rowB n i hi) (rowA n i hi) =
      lowerLineMatrix i hi (T (-1) : R[T;T⁻¹]) (rowA n i hi) (rowA n i hi) := by
    rw [lowerLineMatrix_apply_BA, lowerLineMatrix_apply_self, ← T_add, add_neg_cancel, T_zero]
  have hβ := blockTriangular_transvection_perm_inv_mul i hi _ hG₁b (T 1) hσ
  have hβdet : IsUnit ((upperLineMatrix i hi (T 1 : R[T;T⁻¹]))⁻¹ *
      lowerLineMatrix i hi (T (-1) : R[T;T⁻¹])).det := by
    rw [Matrix.det_mul]
    exact (Matrix.isUnit_nonsing_inv_det _ hG₂).mul hG₁
  have hG : upperLineMatrix i hi (T 1 : R[T;T⁻¹]) * ((upperLineMatrix i hi (T 1 : R[T;T⁻¹]))⁻¹ *
      lowerLineMatrix i hi (T (-1) : R[T;T⁻¹])) = lowerLineMatrix i hi (T (-1) : R[T;T⁻¹]) :=
    Matrix.mul_nonsing_inv_cancel_left _ _ hG₂
  have hGdet : IsUnit (upperLineMatrix i hi (T 1 : R[T;T⁻¹]) *
      ((upperLineMatrix i hi (T 1 : R[T;T⁻¹]))⁻¹ *
        lowerLineMatrix i hi (T (-1) : R[T;T⁻¹]))).det := by
    rw [hG]
    exact hG₁
  have hGb : (upperLineMatrix i hi (T 1 : R[T;T⁻¹]) *
      ((upperLineMatrix i hi (T 1 : R[T;T⁻¹]))⁻¹ *
        lowerLineMatrix i hi (T (-1) : R[T;T⁻¹]))).BlockTriangular (parabolicBlock n i) := by
    rw [hG]
    exact hG₁b
  have e := hf.eval_mul _ _ hG₂ (upperLineMatrix_blockTriangular i hi _) hβdet hβ hGdet hGb
  -- the value of the character at `β = G₂⁻¹ G₁`
  let uβ : Fin n → R[T;T⁻¹]ˣ := fun k =>
    if k = rowA n i hi then laurentT⁻¹ else if k = rowB n i hi then -laurentT else 1
  have huA : uβ (rowA n i hi) = laurentT⁻¹ := by simp [uβ]
  have huB : uβ (rowB n i hi) = -laurentT := by simp [uβ, (rowA_ne_rowB n i hi).symm]
  have huO : ∀ k, k ≠ rowA n i hi ∧ k ≠ rowB n i hi → uβ k = 1 := fun k hk => by
    simp [uβ, hk.1, hk.2]
  have huβ : ∀ k, (uβ k : R[T;T⁻¹]) = ((upperLineMatrix i hi (T 1 : R[T;T⁻¹]))⁻¹ *
      lowerLineMatrix i hi (T (-1) : R[T;T⁻¹])) k k := by
    intro k
    rw [upperLineMatrix_inv_mul_lowerLineMatrix_apply_self]
    by_cases hA : k = rowA n i hi
    · rw [hA, huA, ite_eq_left_of_eq_true _ _ (eq_self _)]
      exact val_laurentT_inv
    · by_cases hB : k = rowB n i hi
      · rw [hB, huB, ite_eq_right_of_eq_false _ _ (eq_false (rowA_ne_rowB n i hi).symm),
          ite_eq_left_of_eq_true _ _ (eq_self _), Units.val_neg, IsUnit.unit_spec]
      · rw [huO k ⟨hA, hB⟩, ite_eq_right_of_eq_false _ _ (eq_false hA),
          ite_eq_right_of_eq_false _ _ (eq_false hB), Units.val_one]
  rw [borelPointOfMatrix_inv_borelCharacterUnit _ hβdet hβ uβ huβ η,
    parabolicPointOfMatrix_congr i hG hGdet hGb hG₁ hG₁b] at e
  have h1 : parabolicPointOfMatrix i (lowerLineMatrix i hi (T (-1) : R[T;T⁻¹])) hG₁ hG₁b f =
      invert (toLaurent (lowerEval R i hi f)) := by
    have hφ : ((invert : R[T;T⁻¹] ≃ₐ[R] R[T;T⁻¹]).toAlgHom.comp toLaurentAlg) X = T (-1) := by
      rw [AlgHom.comp_apply, Polynomial.toLaurentAlg_apply, Polynomial.toLaurent_X]
      exact invert_T 1
    rw [← parabolicPointOfMatrix_congr i (congrArg (lowerLineMatrix i hi) hφ)
      (isUnit_det_lowerLineMatrix i hi _) (lowerLineMatrix_blockTriangular i hi _) hG₁ hG₁b,
      ← comp_lowerEval]
    rfl
  have h2 : parabolicPointOfMatrix i (upperLineMatrix i hi (T 1 : R[T;T⁻¹])) hG₂
      (upperLineMatrix_blockTriangular i hi _) f = toLaurent (upperEval R i hi f) := by
    have hφ : (toLaurentAlg : R[X] →ₐ[R] R[T;T⁻¹]) X = T 1 := by
      rw [Polynomial.toLaurentAlg_apply, Polynomial.toLaurent_X]
    rw [← parabolicPointOfMatrix_congr i (congrArg (upperLineMatrix i hi) hφ)
      (isUnit_det_upperLineMatrix i hi _) (upperLineMatrix_blockTriangular i hi _) hG₂
      (upperLineMatrix_blockTriangular i hi _), ← comp_upperEval]
    rfl
  rw [h1, h2] at e
  -- `∏ₖ uₖ^{ηₖ} = (±1) T^d`
  have hprod : (((∏ k, uβ k ^ η k : R[T;T⁻¹]ˣ)) : R[T;T⁻¹]) =
      toLaurent (((-1 : R[X]ˣ) ^ η (rowB n i hi) : R[X]ˣ) : R[X]) *
        T (η (rowB n i hi) - η (rowA n i hi)) := by
    rw [Fintype.prod_eq_mul (rowA n i hi) (rowB n i hi) (rowA_ne_rowB n i hi)
        (fun k hk => by rw [huO k hk, one_zpow]), huA, huB, ← neg_one_mul laurentT,
      mul_zpow (-1 : R[T;T⁻¹]ˣ) laurentT, inv_zpow' laurentT, Units.val_mul, Units.val_mul,
      val_laurentT_zpow, val_laurentT_zpow, val_neg_one_zpow, sub_eq_add_neg, T_add]
    ring
  have hs : toLaurent (((-1 : R[X]ˣ) ^ η (rowB n i hi) : R[X]ˣ) : R[X]) *
      toLaurent ((((-1 : R[X]ˣ) ^ η (rowB n i hi))⁻¹ : R[X]ˣ) : R[X]) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [map_mul, e]
  exact mul_eq_of_units (Units.inv_mul _) hprod hs

/-- **A Laurent comparison**: if `ψ(T) = T^d φ(T⁻¹)` with `ψ` a polynomial, then `deg φ ≤ d`. -/
theorem eq_zero_or_natDegree_le_of_toLaurent {φ ψ : R[X]} {d : ℤ}
    (h : toLaurent ψ = invert (toLaurent φ) * T d) : φ = 0 ∨ (φ.natDegree : ℤ) ≤ d := by
  by_contra hcon
  rw [not_or, not_le] at hcon
  obtain ⟨hφ, hlt⟩ := hcon
  set m : ℕ := ((φ.natDegree : ℤ) - d).toNat with hm_def
  have hm : (m : ℤ) = φ.natDegree - d := Int.toNat_of_nonneg (by omega)
  have key : toLaurent (ψ * X ^ m) = toLaurent φ.reverse := by
    rw [map_mul, Polynomial.toLaurent_X_pow, h, toLaurent_reverse, mul_assoc, ← T_add]
    congr 2
    omega
  have h0 := Polynomial.ext_iff.mp (Polynomial.toLaurent_injective key) 0
  rw [Polynomial.coeff_mul_X_pow', Polynomial.coeff_zero_reverse] at h0
  split_ifs at h0 with hle
  · omega
  · exact Polynomial.leadingCoeff_ne_zero.mpr hφ h0.symm

/-- **The degree bound**: `deg f(1 + τ E_{i+1,i}) ≤ η_{i+1} - ηᵢ`. -/
theorem lowerEval_mem_degreeLT (hf : IsParabolicSemiInvariant η f) :
    lowerEval R i hi f ∈ degreeLT R (η (rowB n i hi) - η (rowA n i hi) + 1).toNat := by
  rw [mem_degreeLT]
  rcases eq_zero_or_natDegree_le_of_toLaurent (toLaurent_upperEval i hi hf) with h | h
  · rw [h, Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _
  · refine (degree_le_natDegree).trans_lt ?_
    exact_mod_cast (by omega : (lowerEval R i hi f).natDegree <
      (η (rowB n i hi) - η (rowA n i hi) + 1).toNat)

/-! ### Injectivity -/

/-- A function vanishing on both basic open sets of a coprime pair vanishes. -/
theorem eq_zero_of_isCoprime {A : Type*} [CommRing A] {a c x : A} (h : IsCoprime a c)
    (ha : algebraMap A (Localization.Away a) x = 0)
    (hc : algebraMap A (Localization.Away c) x = 0) : x = 0 := by
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers a) _ x).mp ha
  obtain ⟨⟨_, l, rfl⟩, hl⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers c) _ x).mp hc
  obtain ⟨u, v, huv⟩ := h.pow (m := k) (n := l)
  calc x = (u * a ^ k + v * c ^ l) * x := by rw [huv, one_mul]
    _ = u * (a ^ k * x) + v * (c ^ l * x) := by ring
    _ = 0 := by rw [hk, hl, mul_zero, mul_zero, add_zero]

/-- If `f` is semi-invariant and `g ∈ Pᵢ(S)` lies in the coset of `B` of the generic point over
`S`, then `f(g) = 0` implies that `f` vanishes in `S`. -/
theorem algebraMap_eq_zero_of_eval_eq_zero {S : Type u} [CommRing S] [Algebra R S]
    [Algebra (ParabolicCoord R n i) S] [IsScalarTower R (ParabolicCoord R n i) S]
    (hf : IsParabolicSemiInvariant η f) (g : Matrix (Fin n) (Fin n) S) (hg : IsUnit g.det)
    (hgb : g.BlockTriangular (parabolicBlock n i))
    (hb : (g⁻¹ * (parabolicMatrix R n i).map (algebraMap (ParabolicCoord R n i) S)).BlockTriangular
      id)
    (h0 : parabolicPointOfMatrix i g hg hgb f = 0) :
    algebraMap (ParabolicCoord R n i) S f = 0 := by
  set P' := (parabolicMatrix R n i).map (algebraMap (ParabolicCoord R n i) S)
  have hP'det : IsUnit P'.det := isUnit_det_map_ringHom _ (isUnit_det_parabolicMatrix R n i)
  have hP'b : P'.BlockTriangular (parabolicBlock n i) := fun r c h => by
    simp [P', Matrix.map_apply, parabolicMatrix_blockTriangular R n i h]
  have hbdet : IsUnit (g⁻¹ * P').det := by
    rw [Matrix.det_mul]
    exact (Matrix.isUnit_nonsing_inv_det _ hg).mul hP'det
  have hgb' : g * (g⁻¹ * P') = P' := Matrix.mul_nonsing_inv_cancel_left _ _ hg
  have h1 : IsUnit (g * (g⁻¹ * P')).det := by
    rw [hgb']
    exact hP'det
  have h2 : (g * (g⁻¹ * P')).BlockTriangular (parabolicBlock n i) := by
    rw [hgb']
    exact hP'b
  have e := hf.eval_mul g (g⁻¹ * P') hg hgb hbdet hb h1 h2
  have hι : parabolicPointOfMatrix i (g * (g⁻¹ * P')) h1 h2 =
      IsScalarTower.toAlgHom R (ParabolicCoord R n i) S := by
    apply parabolicMatrix_algHom_ext
    rw [parabolicMatrix_map_parabolicPointOfMatrix, hgb']
    rfl
  rw [hι, h0, zero_mul] at e
  exact e

/-- **Injectivity**: a semi-invariant vanishing on the line `1 + τ E_{i+1,i}` vanishes. -/
theorem eq_zero_of_lowerEval_eq_zero (hf : IsParabolicSemiInvariant η f)
    (h0 : lowerEval R i hi f = 0) : f = 0 := by
  have hu : upperEval R i hi f = 0 := by
    have h := toLaurent_upperEval i hi hf
    rw [h0, map_zero, map_zero, zero_mul] at h
    exact (Units.mul_left_eq_zero _).mp
      (Polynomial.toLaurent_injective (h.trans (map_zero (toLaurent (R := R))).symm))
  set a := parabolicMatrix R n i (rowA n i hi) (rowA n i hi)
  set c := parabolicMatrix R n i (rowB n i hi) (rowA n i hi)
  have hcop : IsCoprime a c := isCoprime_mk_parabolic R n i hi le_rfl
  refine eq_zero_of_isCoprime hcop ?_ ?_
  · -- the open set `pᵢᵢ ≠ 0`
    set t : Localization.Away a :=
      algebraMap _ (Localization.Away a) c * IsLocalization.Away.invSelf a
    have hτ : (aeval t : R[X] →ₐ[R] Localization.Away a) X *
        (parabolicMatrix R n i).map (algebraMap _ (Localization.Away a))
          (rowA n i hi) (rowA n i hi) =
        (parabolicMatrix R n i).map (algebraMap _ (Localization.Away a))
          (rowB n i hi) (rowA n i hi) := by
      rw [aeval_X, Matrix.map_apply, Matrix.map_apply, mul_assoc,
        mul_comm (IsLocalization.Away.invSelf a), IsLocalization.Away.mul_invSelf, mul_one]
    refine algebraMap_eq_zero_of_eval_eq_zero i hf _ (isUnit_det_lowerLineMatrix i hi _)
      (lowerLineMatrix_blockTriangular i hi _)
      (blockTriangular_transvection_inv_mul i hi _ ?_ _ hτ) ?_
    · exact fun r c h => by simp [Matrix.map_apply, parabolicMatrix_blockTriangular R n i h]
    · rw [← comp_lowerEval, AlgHom.comp_apply, h0, map_zero]
  · -- the open set `p_{i+1,i} ≠ 0`
    set s : Localization.Away c :=
      algebraMap _ (Localization.Away c) a * IsLocalization.Away.invSelf c
    have hσ : (aeval s : R[X] →ₐ[R] Localization.Away c) X *
        (parabolicMatrix R n i).map (algebraMap _ (Localization.Away c))
          (rowB n i hi) (rowA n i hi) =
        (parabolicMatrix R n i).map (algebraMap _ (Localization.Away c))
          (rowA n i hi) (rowA n i hi) := by
      rw [aeval_X, Matrix.map_apply, Matrix.map_apply, mul_assoc,
        mul_comm (IsLocalization.Away.invSelf c), IsLocalization.Away.mul_invSelf, mul_one]
    refine algebraMap_eq_zero_of_eval_eq_zero i hf _ (isUnit_det_upperLineMatrix i hi _)
      (upperLineMatrix_blockTriangular i hi _)
      (blockTriangular_transvection_perm_inv_mul i hi _ ?_ _ hσ) ?_
    · exact fun r c h => by simp [Matrix.map_apply, parabolicMatrix_blockTriangular R n i h]
    · rw [← comp_upperEval, AlgHom.comp_apply, hu, map_zero]

/-! ### The sections `U · pᵢᵢ^{d-k} p_{i+1,i}^k` -/

/-- A bound `m ≥ ηⱼ` for all `j`. -/
def weightBound (η : Fin n → ℤ) : ℕ :=
  ∑ j, (η j).toNat

theorem le_weightBound (η : Fin n → ℤ) (j : Fin n) : η j ≤ weightBound η := by
  have h : (η j).toNat ≤ weightBound η :=
    Finset.single_le_sum (f := fun j => (η j).toNat) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
  exact (Int.self_le_toNat _).trans (by exact_mod_cast h)

variable (R) in
/-- The determinant of `Pᵢ`, a unit. -/
abbrev parabolicDetUnit : (ParabolicCoord R n i)ˣ :=
  (isUnit_det_parabolicMatrix R n i).unit

/-- The exponent of `pⱼⱼ` in `U`. -/
def diagExponent (η : Fin n → ℤ) (j : Fin n) : ℕ :=
  if j = rowA n i hi ∨ j = rowB n i hi then 0 else (weightBound η - η j).toNat

variable (R) in
/-- The factor `U = det⁻ᵐ · ∏_{j ≠ i, i+1} pⱼⱼ^{m - ηⱼ} · Δ^{m - η_{i+1}}` (`m = weightBound η`),
semi-invariant of weight `(η₀, …, η_{i-1}, η_{i+1}, η_{i+1}, η_{i+2}, …)`. -/
def simpleSemiInvariantFactor (η : Fin n → ℤ) : ParabolicCoord R n i :=
  (((parabolicDetUnit R i)⁻¹ : (ParabolicCoord R n i)ˣ) : ParabolicCoord R n i) ^ weightBound η *
      (∏ j, parabolicMatrix R n i j j ^ diagExponent i hi η j) *
    parabolicMinor (R := R) hi ^ (weightBound η - η (rowB n i hi)).toNat

variable (R) in
/-- **The section corresponding to `τᵏ`**: `U · pᵢᵢ^{d-k} p_{i+1,i}^k`, `d = η_{i+1} - ηᵢ`. -/
def simpleSemiInvariant (η : Fin n → ℤ) (k : ℕ) : ParabolicCoord R n i :=
  simpleSemiInvariantFactor R i hi η *
      parabolicMatrix R n i (rowA n i hi) (rowA n i hi) ^
        ((η (rowB n i hi) - η (rowA n i hi)).toNat - k) *
    parabolicMatrix R n i (rowB n i hi) (rowA n i hi) ^ k

theorem isParabolicSemiInvariant_diag (j : Fin n) (hj : ¬(j = rowA n i hi ∨ j = rowB n i hi)) :
    IsParabolicSemiInvariant (-Pi.single j 1) (parabolicMatrix R n i j j) := by
  refine isParabolicSemiInvariant_entry j j fun k hk => ?_
  have hk' : k.val < j.val := hk
  have hjB : j.val ≠ i + 1 := fun h => hj (Or.inr (Fin.ext h))
  unfold parabolicBlock
  split_ifs <;> omega

theorem isParabolicSemiInvariant_column (r : Fin n) (hr : r = rowA n i hi ∨ r = rowB n i hi) :
    IsParabolicSemiInvariant (-Pi.single (rowA n i hi) 1)
      (parabolicMatrix R n i r (rowA n i hi)) := by
  refine isParabolicSemiInvariant_entry r _ fun k hk => ?_
  have hk' : k.val < i := hk
  have hr' : r.val = i ∨ r.val = i + 1 := by
    rcases hr with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  unfold parabolicBlock
  split_ifs <;> omega

theorem isParabolicSemiInvariant_diagPow (η : Fin n → ℤ) (j : Fin n) :
    IsParabolicSemiInvariant (diagExponent i hi η j • -Pi.single j 1)
      (parabolicMatrix R n i j j ^ diagExponent i hi η j) := by
  by_cases hj : j = rowA n i hi ∨ j = rowB n i hi
  · have he : diagExponent i hi η j = 0 := by simp [diagExponent, hj]
    rw [he, pow_zero, zero_smul]
    exact IsParabolicSemiInvariant.one
  · exact (isParabolicSemiInvariant_diag i hi j hj).pow _

theorem sum_diagExponent_smul (η : Fin n → ℤ) :
    ∑ j, diagExponent i hi η j • (-Pi.single j 1 : Fin n → ℤ) =
      fun j => -(diagExponent i hi η j : ℤ) := by
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/-- **`U · pᵢᵢ^{d-k} p_{i+1,i}^k` is a section of `𝓛(η)` over `X_{sᵢ}`** (for `0 ≤ k ≤ d`). -/
theorem isParabolicSemiInvariant_simpleSemiInvariant (η : Fin n → ℤ) (k : ℕ)
    (hk : k ≤ (η (rowB n i hi) - η (rowA n i hi)).toNat)
    (hd : 0 ≤ η (rowB n i hi) - η (rowA n i hi)) :
    IsParabolicSemiInvariant η (simpleSemiInvariant R i hi η k) := by
  have hdet : IsParabolicSemiInvariant (-1)
      ((parabolicDetUnit R i : (ParabolicCoord R n i)ˣ) : ParabolicCoord R n i) := by
    rw [IsUnit.unit_spec]
    exact isParabolicSemiInvariant_det
  have h := ((((hdet.inv.pow (weightBound η)).mul (IsParabolicSemiInvariant.prod Finset.univ
    fun j _ => isParabolicSemiInvariant_diagPow i hi η j)).mul
    ((isParabolicSemiInvariant_parabolicMinor (R := R) hi).pow
      (weightBound η - η (rowB n i hi)).toNat)).mul
    ((isParabolicSemiInvariant_column i hi (R := R) _ (Or.inl rfl)).pow
      ((η (rowB n i hi) - η (rowA n i hi)).toNat - k))).mul
    ((isParabolicSemiInvariant_column i hi (R := R) _ (Or.inr rfl)).pow k)
  rw [sum_diagExponent_smul] at h
  rw [simpleSemiInvariant, simpleSemiInvariantFactor]
  convert h using 1
  funext j
  have hm := le_weightBound η j
  have hmB := le_weightBound η (rowB n i hi)
  have hAB := rowA_ne_rowB n i hi
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.sub_apply, Pi.one_apply,
    Pi.single_apply, neg_neg]
  simp only [nsmul_eq_mul]
  by_cases hA : j = rowA n i hi
  · subst hA
    have he : diagExponent i hi η (rowA n i hi) = 0 := by simp [diagExponent]
    simp only [he, hAB, ↓reduceIte]
    omega
  · by_cases hB : j = rowB n i hi
    · subst hB
      have he : diagExponent i hi η (rowB n i hi) = 0 := by simp [diagExponent]
      simp only [he, Ne.symm hAB, ↓reduceIte]
      omega
    · have he : (diagExponent i hi η j : ℤ) = weightBound η - η j := by
        simp only [diagExponent, hA, hB, or_self, ↓reduceIte]
        omega
      simp only [hA, hB, ↓reduceIte]
      omega

theorem lowerEval_det :
    lowerEval R i hi (parabolicMatrix R n i).det = 1 := by
  rw [show lowerEval R i hi (parabolicMatrix R n i).det =
      ((parabolicMatrix R n i).map (lowerEval R i hi)).det from
      (det_map_ringHom (B := R[X]) (lowerEval R i hi).toRingHom _).symm, lowerEval,
    parabolicMatrix_map_parabolicPointOfMatrix, det_lowerLineMatrix]

/-- **`U · pᵢᵢ^{d-k} p_{i+1,i}^k` restricts to `τᵏ`.** -/
theorem lowerEval_simpleSemiInvariant (η : Fin n → ℤ) (k : ℕ) :
    lowerEval R i hi (simpleSemiInvariant R i hi η k) = X ^ k := by
  have hinv : lowerEval R i hi
      (((parabolicDetUnit R i)⁻¹ : (ParabolicCoord R n i)ˣ) : ParabolicCoord R n i) = 1 := by
    have h := congrArg (lowerEval R i hi) (Units.inv_mul (parabolicDetUnit R i))
    rw [map_mul, IsUnit.unit_spec, lowerEval_det, mul_one, map_one] at h
    exact h
  simp only [simpleSemiInvariant, simpleSemiInvariantFactor, parabolicMinor, map_mul, map_pow,
    map_prod, map_sub, hinv, lowerEval_parabolicMatrix, lowerLineMatrix_apply_self,
    lowerLineMatrix_apply_BA, lowerLineMatrix_apply_AB, one_pow, Finset.prod_const_one, mul_one,
    one_mul, zero_mul, sub_zero]

/-! ### `H⁰(X_{sᵢ}, 𝓛(η))` -/

variable (R) in
/-- Restriction to the line `1 + τ E_{i+1,i}`, on the semi-invariants of weight `η`. -/
def lowerEvalSemiInvariants (η : Fin n → ℤ) :
    quotientSemiInvariants R n (parabolicIdeal R n i) η →ₗ[R]
      degreeLT R (η (rowB n i hi) - η (rowA n i hi) + 1).toNat :=
  LinearMap.codRestrict _
    ((lowerEval R i hi).toLinearMap ∘ₗ
        (quotientSemiInvariants R n (parabolicIdeal R n i) η).subtype)
    fun f => lowerEval_mem_degreeLT i hi ((mem_quotientSemiInvariants_parabolicIdeal_iff η f.1).mp
        f.2)

theorem lowerEvalSemiInvariants_apply (η : Fin n → ℤ)
    (f : quotientSemiInvariants R n (parabolicIdeal R n i) η) :
    (lowerEvalSemiInvariants R i hi η f : R[X]) = lowerEval R i hi f :=
  rfl

theorem lowerEvalSemiInvariants_bijective (η : Fin n → ℤ) :
    Function.Bijective (lowerEvalSemiInvariants R i hi η) := by
  classical
  refine ⟨(injective_iff_map_eq_zero _).mpr fun f hf => Subtype.ext ?_, fun φ => ?_⟩
  · exact eq_zero_of_lowerEval_eq_zero i hi
      ((mem_quotientSemiInvariants_parabolicIdeal_iff η f.1).mp f.2)
      (congrArg Subtype.val hf)
  · have hle : degreeLT R (η (rowB n i hi) - η (rowA n i hi) + 1).toNat ≤
        LinearMap.range ((lowerEval R i hi).toLinearMap ∘ₗ
          (quotientSemiInvariants R n (parabolicIdeal R n i) η).subtype) := by
      rw [degreeLT_eq_span_X_pow, Submodule.span_le]
      intro p hp
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hp)
      have hk' := Finset.mem_range.mp hk
      have hd : 0 ≤ η (rowB n i hi) - η (rowA n i hi) := by omega
      refine ⟨⟨simpleSemiInvariant R i hi η k,
          (mem_quotientSemiInvariants_parabolicIdeal_iff η _).mpr
        (isParabolicSemiInvariant_simpleSemiInvariant i hi η k (by omega) hd)⟩, ?_⟩
      exact lowerEval_simpleSemiInvariant i hi η k
    obtain ⟨f, hf⟩ := hle φ.2
    exact ⟨f, Subtype.ext hf⟩

/-- The equality of ideals `J = J'` identifies the semi-invariants. -/
def semiInvariantsEquivOfEq {J J' : Ideal (GLCoord R n)} (h : J = J') (η : Fin n → ℤ) :
    quotientSemiInvariants R n J η ≃ₗ[R] quotientSemiInvariants R n J' η := by
  subst h
  exact LinearEquiv.refl R _

variable (R) in
/-- **The semi-invariants of weight `η` on `Pᵢ`**: `(𝒪(Pᵢ))^{(B, η)} ≅ R[τ]_{< d + 1}`. -/
def parabolicSemiInvariantsEquiv (η : Fin n → ℤ) :
    quotientSemiInvariants R n (parabolicIdeal R n i) η ≃ₗ[R]
      degreeLT R (η (rowB n i hi) - η (rowA n i hi) + 1).toNat :=
  LinearEquiv.ofBijective _ (lowerEvalSemiInvariants_bijective i hi η)

variable (R) in
/-- **`H⁰(X_{sᵢ}, 𝓛(η)) ≅ R[τ]_{< d + 1}`**, `d = η_{i+1} - ηᵢ = -⟨η, αᵢ^∨⟩`:
`sectionsEquivSemiInvariants` and
`π⁻¹(X_{sᵢ}) = Pᵢ`, followed by `f ↦ f(1 + τ E_{i+1,i})`. -/
def simpleSchubertSectionsEquiv (η : Fin n → ℤ) :
    sections R n (simpleSchubert R n i hi) η ≃ₗ[R]
      degreeLT R (η (rowB n i hi) - η (rowA n i hi) + 1).toNat :=
  (sectionsEquivSemiInvariants R n _ η).trans
    ((semiInvariantsEquivOfEq (preimageIdeal_simpleSchubert R n i hi) η).trans
      (parabolicSemiInvariantsEquiv R i hi η))

instance (η : Fin n → ℤ) : Module.Free R (sections R n (simpleSchubert R n i hi) η) :=
  Module.Free.of_equiv ((simpleSchubertSectionsEquiv R i hi η).trans (degreeLTEquiv R _)).symm

instance (η : Fin n → ℤ) : Module.Finite R (sections R n (simpleSchubert R n i hi) η) :=
  Module.Finite.equiv ((simpleSchubertSectionsEquiv R i hi η).trans (degreeLTEquiv R _)).symm

/-- **`H⁰(X_{sᵢ}, 𝓛(η))` is free of rank `max(0, η_{i+1} - ηᵢ + 1)`.** -/
theorem finrank_sections_simpleSchubert [Nontrivial R] (η : Fin n → ℤ) :
    Module.finrank R (sections R n (simpleSchubert R n i hi) η) =
      (η (rowB n i hi) - η (rowA n i hi) + 1).toNat := by
  rw [((simpleSchubertSectionsEquiv R i hi η).trans (degreeLTEquiv R _)).finrank_eq,
    Module.finrank_fin_fun]

/-- `H⁰(X_{sᵢ}, 𝓛(η)) = 0` when `η_{i+1} < ηᵢ`. -/
theorem subsingleton_sections_simpleSchubert (η : Fin n → ℤ)
    (h : η (rowB n i hi) < η (rowA n i hi)) :
    Subsingleton (sections R n (simpleSchubert R n i hi) η) := by
  have h0 : (η (rowB n i hi) - η (rowA n i hi) + 1).toNat = 0 := by omega
  refine (simpleSchubertSectionsEquiv R i hi η).toEquiv.subsingleton_congr.mpr ?_
  rw [h0]
  have key : ∀ p : degreeLT R 0, (p : R[X]) = 0 := fun p => by
    by_contra hp
    have h2 := mem_degreeLT.mp p.2
    rw [Polynomial.degree_eq_natDegree hp] at h2
    exact Nat.not_lt_zero _ (by exact_mod_cast h2)
  exact ⟨fun a b => Subtype.ext ((key a).trans (key b).symm)⟩

end FlagVarieties
