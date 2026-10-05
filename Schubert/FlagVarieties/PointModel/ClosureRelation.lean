import Schubert.FlagVarieties.PointModel.UnitIdeal
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# The closure relation in `𝒪(GL_n)`

`cellIdeal K w` is the ideal of the functions in `𝒪(GL_n)` vanishing on the single Bruhat cell
`B ẇ B`. The **closure relation** (`cellIdeal_le_cellIdeal`): if `v ≤ w` in Bruhat order, every
function vanishing on `B ẇ B` vanishes on `B v̇ B`. Hence (`orbitIdeal_lowerSet`) the ideal of
`π⁻¹ X_w = ⋃_{v ≤ w} B v̇ B` is the ideal of the single cell `B ẇ B`, i.e. of the orbit map
`(b, b') ↦ b ẇ b'`.

The proof transfers the Demazure library's closure relation on the flag-minor algebra
(`flagOrbitRestriction_zero_of_bruhat_columns`) to `𝒪(GL_n)`, chart by chart: on the big cell
`G_v`, `g = L(g) β(g)⁻¹`; expanding `r(L · b)` in the entries of the upper-triangular `b` gives
coefficients `P_α(L)`, which are homogenized into the flag-minor algebra (`exists_homogenize_poly`).
-/

open Schubert Demazure.FlagModule Demazure.SchubertUnions FinPermutation
open GLRep (glEval)

namespace FlagVarieties.PointModel

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {n : ℕ}

/-- The ideal of functions vanishing on the Bruhat cell `B ẇ B`. -/
def cellIdeal (K : Type*) [Field K] (w : Equiv.Perm (Fin n)) : Ideal (GLCoord K n) where
  carrier := {t | ∀ g ∈ bruhatCell K w, glEval g t = 0}
  add_mem' {a b} ha hb g hg := by rw [map_add, ha g hg, hb g hg, add_zero]
  zero_mem' g _ := map_zero _
  smul_mem' c a ha g hg := by rw [smul_eq_mul, map_mul, ha g hg, mul_zero]

theorem mem_cellIdeal {w : Equiv.Perm (Fin n)} {t : GLCoord K n} :
    t ∈ cellIdeal K w ↔ ∀ g ∈ bruhatCell K w, glEval g t = 0 :=
  Iff.rfl

theorem orbitSet_singleton (w : Equiv.Perm (Fin n)) : orbitSet K {w} = bruhatCell K w := by
  ext g
  simp [orbitSet]

/-! ### Expansion in the entries of an upper-triangular matrix -/

/-- The upper-triangular part of an assignment `y`. -/
def upperPart (y : Fin n × Fin n → K) : Matrix (Fin n) (Fin n) K :=
  fun k j => if k ≤ j then y (k, j) else 0

theorem upperPart_isUpperTriangular (y : Fin n × Fin n → K) : (upperPart y).IsUpperTriangular := by
  intro k j hjk
  have : ¬ k ≤ j := not_le.mpr hjk
  simp [upperPart, this]

/-- The generic upper-triangular entry `b_kj`. -/
def upperVar (k j : Fin n) : MvPolynomial (Fin n × Fin n) (MatrixEntryPolynomial K n) :=
  if k ≤ j then MvPolynomial.X (k, j) else 0

/-- `r(x · b)`, as a polynomial in the entries `b_kj` (`k ≤ j`) with coefficients in `K[x_ij]`. -/
def rightExpand (r : MatrixEntryPolynomial K n) : MvPolynomial (Fin n × Fin n)
    (MatrixEntryPolynomial K n) :=
  MvPolynomial.aeval (fun ij : Fin n × Fin n =>
    ∑ k, MvPolynomial.C (MvPolynomial.X (ij.1, k)) * upperVar k ij.2) r

theorem eval_map_rightExpand (X : Matrix (Fin n) (Fin n) K) (y : Fin n × Fin n → K)
    (r : MatrixEntryPolynomial K n) :
    MvPolynomial.eval y (MvPolynomial.map (evalAt X).toRingHom (rightExpand r)) =
      evalAt (X * upperPart y) r := by
  induction r using MvPolynomial.induction_on with
  | C a => simp [rightExpand, evalAt]
  | add p q hp hq => rw [rightExpand, map_add, ← rightExpand, ← rightExpand, map_add, map_add, hp,
      hq, map_add]
  | mul_X p ij hp =>
    rw [rightExpand, map_mul, ← rightExpand, map_mul, map_mul, hp, map_mul, evalAt_X,
      MvPolynomial.aeval_X, Matrix.mul_apply, map_sum, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [upperVar, upperPart, map_mul, MvPolynomial.map_C, MvPolynomial.eval_C]
    split_ifs <;> simp [evalAt]

/-- A polynomial vanishing at every assignment with nonzero diagonal entries is zero. -/
theorem eq_zero_of_eval_diag_ne_zero [Infinite K] {q : MvPolynomial (Fin n × Fin n) K}
    (h : ∀ y : Fin n × Fin n → K, (∀ k, y (k, k) ≠ 0) → MvPolynomial.eval y q = 0) : q = 0 := by
  classical
  let s : Fin n × Fin n → Set K := fun ij => if ij.1 = ij.2 then {0}ᶜ else Set.univ
  have hs : ∀ ij, (s ij).Infinite := by
    intro ij
    by_cases hij : ij.1 = ij.2
    · simp only [s, ite_eq_left hij]
      exact (Set.finite_singleton (0 : K)).infinite_compl
    · simp only [s, ite_eq_right hij]
      exact Set.infinite_univ
  refine MvPolynomial.funext_set s hs fun y hy => ?_
  rw [map_zero]
  refine h y fun k => ?_
  have := hy (k, k) (Set.mem_univ _)
  simpa [s] using this

/-! ### The closure relation -/

theorem coeff_rightExpand_eq_zero [Infinite K] {w : Equiv.Perm (Fin n)}
    {r : MatrixEntryPolynomial K n}
    (hr : ∀ g ∈ bruhatCell K w, evalAt (g : Matrix (Fin n) (Fin n) K) r = 0)
    (α : (Fin n × Fin n) →₀ ℕ) {g : GL (Fin n) K} (hg : g ∈ bruhatCell K w) :
    evalAt (g : Matrix (Fin n) (Fin n) K) ((rightExpand r).coeff α) = 0 := by
  have hq :
      MvPolynomial.map (evalAt (g : Matrix (Fin n) (Fin n) K)).toRingHom (rightExpand r) = 0 := by
    refine eq_zero_of_eval_diag_ne_zero fun y hy => ?_
    rw [eval_map_rightExpand]
    have hdet : IsUnit (upperPart y).det := by
      rw [Matrix.det_of_isUpperTriangular (upperPart_isUpperTriangular y)]
      refine isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => ?_)
      simpa [upperPart] using hy k
    have hb : IsBorel (unitOfDet (upperPart y) hdet) := by
      unfold IsBorel
      rw [coe_unitOfDet]
      exact upperPart_isUpperTriangular y
    have := hr _ (bruhatCell_mul_borel hg hb)
    rwa [Units.val_mul, coe_unitOfDet] at this
  have := congrArg (fun q : MvPolynomial (Fin n × Fin n) K => q.coeff α) hq
  simpa [MvPolynomial.coeff_map] using this

theorem evalAt_eq_zero_of_mem_bruhatCell_of_le [Infinite K] (hSMT : StandardMonomialTheory K)
    {w v' : Equiv.Perm (Fin n)} (hv'w : v' ≤ᴮ w)
    {r : MatrixEntryPolynomial K n}
    (hr : ∀ g ∈ bruhatCell K w, evalAt (g : Matrix (Fin n) (Fin n) K) r = 0)
    {g : GL (Fin n) K} (hg : g ∈ bruhatCell K v') :
    evalAt (g : Matrix (Fin n) (Fin n) K) r = 0 := by
  classical
  obtain ⟨v, hv⟩ := exists_chartMinor_ne_zero g
  -- the coefficients `P_α` vanish at `L(g)`
  have hPL : ∀ α, evalAt (chartMatrix K v g) ((rightExpand r).coeff α) = 0 := by
    intro α
    obtain ⟨N, a, ha, hav⟩ := exists_homogenize_poly v ((rightExpand r).coeff α)
    have he : a * chartPoly K v ∈ minorSpan K (N • onesShape n + onesShape n) :=
      mul_mem_minorSpan ha (chartPoly_mem_minorSpan v)
    have hew : ∀ g' ∈ orbitSet K {w},
        evalAt (g' : Matrix (Fin n) (Fin n) K) (a * chartPoly K v) = 0 := by
      intro g' hg'
      rw [orbitSet_singleton] at hg'
      by_cases hg'v : ∀ c, evalAt (g' : Matrix (Fin n) (Fin n) K) (chartMinor K v c) ≠ 0
      · obtain ⟨β, hβdef⟩ : ∃ β : GL (Fin n) K, (β : Matrix (Fin n) (Fin n) K) = chartBeta K v g' :=
          ⟨unitOfDet (chartBeta K v g') (chartBeta_det_isUnit v g' hg'v), coe_unitOfDet _ _⟩
        have hβ : IsBorel β := by
          unfold IsBorel
          rw [hβdef]
          exact chartBeta_isUpperTriangular v (g' : Matrix (Fin n) (Fin n) K)
        have hL := coeff_rightExpand_eq_zero hr α (bruhatCell_mul_borel hg' hβ)
        rw [Units.val_mul, hβdef] at hL
        have hL' : evalAt (chartMatrix K v g') ((rightExpand r).coeff α) = 0 := hL
        rw [map_mul, hav _ hg'v, hL', mul_zero, zero_mul]
      · push Not at hg'v
        obtain ⟨c, hc⟩ := hg'v
        rw [map_mul, chartPoly, map_prod, Finset.prod_eq_zero (Finset.mem_univ c) hc, mul_zero]
    have hz := (forall_mem_orbitSet_iff he {w}).mp hew w (Finset.mem_singleton_self w)
    obtain ⟨d, h, hh⟩ := exists_columnMultiplicity (N • onesShape n + onesShape n)
    have he' : a * chartPoly K v ∈ flagSpan K h := by
      rw [← minorSpan_columnMultiplicity, hh]
      exact he
    have hzv := hSMT.closure h hv'w _ he' hz
    have hg0 := (forall_mem_orbitSet_iff he {v'}).mpr (fun x hx u hu => by
      rw [Finset.mem_singleton] at hx
      subst hx
      exact hzv u hu) g (by rw [orbitSet_singleton]; exact hg)
    rw [map_mul, hav _ hv] at hg0
    have hf : evalAt (g : Matrix (Fin n) (Fin n) K) (chartPoly K v) ≠ 0 := by
      rw [chartPoly, map_prod]
      exact Finset.prod_ne_zero_iff.mpr fun c _ => hv c
    rcases mul_eq_zero.mp hg0 with h1 | h1
    · exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hf)
    · exact absurd h1 hf
  -- reassemble `r(g) = r(L(g) β(g)⁻¹)`
  have hβu : IsUnit (chartBeta K v g).det := chartBeta_det_isUnit v g hv
  have hβinv : ((chartBeta K v g)⁻¹).IsUpperTriangular := by
    have := Matrix.invertibleOfIsUnitDet _ hβu
    exact Matrix.blockTriangular_inv_of_blockTriangular
      (chartBeta_isUpperTriangular v (g : Matrix (Fin n) (Fin n) K))
  let y : Fin n × Fin n → K := fun kj => (chartBeta K v g)⁻¹ kj.1 kj.2
  have hy : upperPart y = (chartBeta K v g)⁻¹ := by
    ext k j
    simp only [upperPart, y]
    split_ifs with hkj
    · rfl
    · exact (hβinv (lt_of_not_ge hkj)).symm
  have hg : (g : Matrix (Fin n) (Fin n) K) = chartMatrix K v g * upperPart y := by
    rw [hy, chartMatrix, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hβu, Matrix.mul_one]
  rw [hg, ← eval_map_rightExpand]
  have hq : MvPolynomial.map (evalAt (chartMatrix K v g)).toRingHom (rightExpand r) = 0 := by
    ext α
    rw [MvPolynomial.coeff_map]
    simpa using hPL α
  rw [hq, map_zero]

/-- **The closure relation**: for `v ≤ w`, functions vanishing on `B ẇ B` vanish on `B v̇ B`. -/
theorem cellIdeal_le_cellIdeal [Infinite K] (hSMT : StandardMonomialTheory K)
    {v w : Equiv.Perm (Fin n)}
    (hvw : v ≤ᴮ w) :
    cellIdeal K w ≤ cellIdeal K v := by
  intro t ht g hg
  obtain ⟨r, k, hrk⟩ := exists_mul_det_pow t
  have hev : ∀ g' : GL (Fin n) K, glEval g' t * (g' : Matrix (Fin n) (Fin n) K).det ^ k =
      evalAt (g' : Matrix (Fin n) (Fin n) K) r := by
    intro g'
    have := congrArg (glEval g') hrk
    rwa [map_mul, glEval_algebraMap_eq_evalAt, glEval_algebraMap_eq_evalAt, map_pow,
        evalAt_genericDetPoly] at this
  have hr : ∀ g' ∈ bruhatCell K w, evalAt (g' : Matrix (Fin n) (Fin n) K) r = 0 := by
    intro g' hg'
    rw [← hev, ht g' hg', zero_mul]
  have h0 := evalAt_eq_zero_of_mem_bruhatCell_of_le hSMT hvw hr hg
  rw [← hev] at h0
  have hdet : (g : Matrix (Fin n) (Fin n) K).det ^ k ≠ 0 :=
    pow_ne_zero _ ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  exact (mul_eq_zero.mp h0).resolve_right hdet

/-- **The ideal of `π⁻¹ X_w` is the ideal of the cell `B ẇ B`.** -/
theorem orbitIdeal_lowerSet [Infinite K] (hSMT : StandardMonomialTheory K)
    (w : Equiv.Perm (Fin n)) :
    orbitIdeal K (lowerSet w) = cellIdeal K w := by
  apply le_antisymm
  · intro t ht g hg
    exact ht g (mem_orbitSet.mpr ⟨w, mem_lowerSet_self w, hg⟩)
  · intro t ht g hg
    obtain ⟨v, hv, hgv⟩ := mem_orbitSet.mp hg
    exact cellIdeal_le_cellIdeal hSMT (mem_lowerSet.mp hv) ht g hgv

end

end FlagVarieties.PointModel
