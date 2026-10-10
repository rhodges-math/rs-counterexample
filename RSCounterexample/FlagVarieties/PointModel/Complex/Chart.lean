import RSCounterexample.FlagVarieties.PointModel.Complex.HyperplaneSection
import Mathlib.Algebra.BigOperators.Field

/-!
# Big cells and homogenization

Fix a permutation `v`. The **big cell** `G_v ⊆ GL_n` is where the flag minors
`D_k = Δ^{0..k}_{v 0, …, v k}` (`chartMinor v k`) do not vanish; `f_v = ∏_k D_k` (`chartPoly v`).
On `G_v` every `g` factors as `g = L(g) b` with `b ∈ B` and `L(g) = g β(g)` (`chartMatrix v g`),
whose entries are ratios of flag minors, `L_rc = Δ^{0..c}_{v 0, …, v (c-1), r}(g) / D_c(g)`
(`chartMatrix_apply`, by Laplace expansion along the last row).

`exists_homogenization`: a function `t ∈ 𝒪(GL_n)` that is semi-invariant of weight
`λ = shapeWeight m` on a right `B`-stable set `Z` agrees on `Z` with `a / f_v^K` for some `K` and
some `a` in the flag-minor algebra of shape `m + K·(1, …, 1)`. This is the ring form of
`A_{(f_v)} ≅ 𝒪(U⁻)` used in the hyperplane step of the proof of projective normality.
-/

open Schubert Demazure.FlagModule Demazure.SchubertUnions FinPermutation
open GLRep (glEval)

namespace FlagVarieties.PointModel.Complex

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

/-- The rows `v 0, …, v k`, in this order. -/
def leadRows (v : Equiv.Perm (Fin n)) (k : Fin n) : Fin (k.val + 1) → Fin n :=
  fun a => v (prefixIndex k a)

/-- `D_k = Δ^{0..k}_{v 0, …, v k}`. -/
def chartMinor (v : Equiv.Perm (Fin n)) (k : Fin n) : MatrixPolynomial n :=
  flagRowMinor k (leadRows v k)

/-- `f_v = ∏_k D_k`; the big cell `G_v` is the locus where `f_v ≠ 0`. -/
def chartPoly (v : Equiv.Perm (Fin n)) : MatrixPolynomial n := ∏ k, chartMinor v k

/-- The rows `v 0, …, v (k-1), r`, in this order. -/
def snocRows (v : Equiv.Perm (Fin n)) (k r : Fin n) : Fin (k.val + 1) → Fin n :=
  fun a => if h : a.val < k.val then v ⟨a.val, by omega⟩ else r

/-- The numerator `Δ^{0..k}_{v 0, …, v (k-1), r}`. -/
def numMinor (v : Equiv.Perm (Fin n)) (r k : Fin n) : MatrixPolynomial n :=
  flagRowMinor k (snocRows v k r)

/-- The column shape `(1, …, 1)`: one column of each height. -/
def onesShape (n : ℕ) : ColumnShape n := fun _ => 1

theorem onesShape_eq_sum (n : ℕ) : onesShape n = ∑ k, Pi.single k 1 := by
  funext i
  simp [onesShape, Finset.sum_apply, Pi.single_apply]

/-- A product of elements of graded pieces lies in the sum of the shapes. -/
theorem prod_mem_minorSpan {ι : Type*} (s : Finset ι) (p : ι → MatrixPolynomial n)
    (m : ι → ColumnShape n) (hp : ∀ i ∈ s, p i ∈ minorSpan (m i)) :
    ∏ i ∈ s, p i ∈ minorSpan (∑ i ∈ s, m i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one_mem_minorSpan
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact mul_mem_minorSpan (hp a (Finset.mem_insert_self a s))
      (ih fun i hi => hp i (Finset.mem_insert_of_mem hi))

theorem chartPoly_mem_minorSpan (v : Equiv.Perm (Fin n)) :
    chartPoly v ∈ minorSpan (onesShape n) := by
  rw [onesShape_eq_sum]
  exact prod_mem_minorSpan _ _ _ fun k _ => flagRowMinor_mem_minorSpan _ _

/-- `Y_rc = Δ^{0..c}_{v 0, …, v (c-1), r} · ∏_{c' ≠ c} D_{c'}`, so that `Y_rc = f_v · L_rc` on
`G_v`. -/
def chartNum (v : Equiv.Perm (Fin n)) (r c : Fin n) : MatrixPolynomial n :=
  numMinor v r c * ∏ c' ∈ Finset.univ.erase c, chartMinor v c'

theorem chartNum_mem_minorSpan (v : Equiv.Perm (Fin n)) (r c : Fin n) :
    chartNum v r c ∈ minorSpan (onesShape n) := by
  classical
  have h := mul_mem_minorSpan (flagRowMinor_mem_minorSpan c (snocRows v c r))
    (prod_mem_minorSpan (Finset.univ.erase c) (chartMinor v) (fun k => Pi.single k 1)
      fun k _ => flagRowMinor_mem_minorSpan _ _)
  rwa [Finset.add_sum_erase Finset.univ (fun i => (Pi.single i 1 : ColumnShape n))
    (Finset.mem_univ c), ← onesShape_eq_sum] at h

/-! ### Laplace expansion along the last row -/

/-- The signed cofactor of the entry `(last, j)` in `Δ^{0..k}_{v 0, …, v (k-1), r}`; it does not
depend on `r`. -/
def chartCof (v : Equiv.Perm (Fin n)) (k : Fin n) (j : Fin (k.val + 1))
    (g : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (-1) ^ (k.val + j.val) *
    (g.submatrix (fun a : Fin k.val => v ⟨a.val, by omega⟩) (prefixIndex k ∘ j.succAbove)).det

theorem evalAt_numMinor (v : Equiv.Perm (Fin n)) (r k : Fin n) (g : Matrix (Fin n) (Fin n) ℂ) :
    evalAt g (numMinor v r k) = ∑ j, g r (prefixIndex k j) * chartCof v k j g := by
  rw [numMinor, evalAt_flagRowMinor, Matrix.det_succ_row _ (Fin.last k.val)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hlast : snocRows v k r (Fin.last k.val) = r := by
    simp [snocRows]
  have hsub : (g.submatrix (snocRows v k r) (prefixIndex k)).submatrix (Fin.last k.val).succAbove
      j.succAbove =
      g.submatrix (fun a : Fin k.val => v ⟨a.val, by omega⟩) (prefixIndex k ∘ j.succAbove) := by
    ext a b
    simp only [Matrix.submatrix_apply, Fin.succAbove_last, Function.comp_apply, snocRows,
      Fin.val_castSucc, a.isLt, dite_eq_left]
  rw [Matrix.submatrix_apply, hlast, hsub, chartCof, Fin.val_last]
  ring

/-- The upper-triangular matrix `β(g)` with `L(g) = g β(g)`. -/
def chartBeta (v : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun l c => if h : l.val ≤ c.val then
    chartCof v c ⟨l.val, by omega⟩ g / evalAt g (chartMinor v c) else 0

theorem chartBeta_isUpperTriangular (v : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) :
    (chartBeta v g).IsUpperTriangular := by
  intro l c hcl
  have : ¬ l.val ≤ c.val := by
    have : c.val < l.val := hcl
    omega
  simp [chartBeta, this]

/-- `L(g) = g β(g)`. -/
def chartMatrix (v : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  g * chartBeta v g

/-- **The entries of `L(g)` are ratios of flag minors.** -/
theorem chartMatrix_apply (v : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) (r c : Fin n) :
    chartMatrix v g r c = evalAt g (numMinor v r c) / evalAt g (chartMinor v c) := by
  classical
  rw [chartMatrix, Matrix.mul_apply, evalAt_numMinor, Finset.sum_div]
  have hsub : ∑ l, g r l * chartBeta v g l c =
      ∑ l ∈ Finset.univ.image (prefixIndex c), g r l * chartBeta v g l c := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun l _ hl => ?_
    have hlc : ¬ l.val ≤ c.val := by
      intro hle
      exact hl (Finset.mem_image.mpr ⟨⟨l.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    simp [chartBeta, hlc]
  rw [hsub, Finset.sum_image (fun a _ b _ h => prefixIndex_injective c h)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : (prefixIndex c j).val ≤ c.val := by
    simp only [prefixIndex]
    omega
  simp only [chartBeta, dite_eq_left hj]
  rw [mul_div_assoc]
  rfl

/-- The rows `v a` with `a < c` of `L(g)` vanish in column `c`. -/
theorem chartMatrix_eq_zero (v : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) {a c : Fin n}
    (hac : a < c) : chartMatrix v g (v a) c = 0 := by
  have hac' : a.val < c.val := hac
  rw [chartMatrix_apply, numMinor, evalAt_flagRowMinor,
    Matrix.det_zero_of_row_eq (i := (⟨a.val, by omega⟩ : Fin (c.val + 1)))
      (j := Fin.last c.val), zero_div]
  · intro h
    have := congrArg Fin.val h
    simp only [Fin.val_last] at this
    omega
  · funext b
    simp [Matrix.submatrix_apply, snocRows, hac']

theorem snocRows_self (v : Equiv.Perm (Fin n)) (c : Fin n) : snocRows v c (v c) = leadRows v c := by
  funext b
  simp only [snocRows, leadRows]
  split_ifs with hb
  · rfl
  · congr 1
    ext
    simp only [prefixIndex]
    have := b.isLt
    omega

/-- The diagonal entries `L_{v c, c}` are `1` on the big cell. -/
theorem chartMatrix_self (v : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) (c : Fin n)
    (hc : evalAt g (chartMinor v c) ≠ 0) : chartMatrix v g (v c) c = 1 := by
  rw [chartMatrix_apply, numMinor, snocRows_self]
  exact div_self hc

theorem det_chartMatrix (v : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ)
    (hg : ∀ c, evalAt g (chartMinor v c) ≠ 0) :
    (Equiv.Perm.sign v : ℂ) * (chartMatrix v g).det = 1 := by
  have hlow : ((chartMatrix v g).submatrix v id).IsLowerTriangular :=
    fun a c hac => chartMatrix_eq_zero v g (OrderDual.toDual_lt_toDual.mp hac)
  have h1 := Matrix.det_permute v (chartMatrix v g)
  rw [Matrix.det_of_isLowerTriangular _ hlow] at h1
  simp only [Matrix.submatrix_apply, id_eq, chartMatrix_self v g _ (hg _),
    Finset.prod_const_one] at h1
  exact h1.symm

theorem det_chartMatrix_ne_zero (v : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ)
    (hg : ∀ c, evalAt g (chartMinor v c) ≠ 0) : (chartMatrix v g).det ≠ 0 := by
  intro h
  have := det_chartMatrix v g hg
  rw [h, mul_zero] at this
  exact zero_ne_one this

/-- `D_c(L(g)) = 1` on the big cell. -/
theorem evalAt_chartMatrix_chartMinor (v : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ)
    (hg : ∀ c, evalAt g (chartMinor v c) ≠ 0) (c : Fin n) :
    evalAt (chartMatrix v g) (chartMinor v c) = 1 := by
  rw [chartMinor, evalAt_flagRowMinor]
  have hlow : ((chartMatrix v g).submatrix (leadRows v c) (prefixIndex c)).IsLowerTriangular := by
    intro a b hab
    have hab' : a < b := OrderDual.toDual_lt_toDual.mp hab
    exact chartMatrix_eq_zero v g (a := prefixIndex c a) (c := prefixIndex c b) (by
      change (prefixIndex c a).val < (prefixIndex c b).val
      simp only [prefixIndex]
      exact hab')
  rw [Matrix.det_of_isLowerTriangular _ hlow]
  exact Finset.prod_eq_one fun a _ => chartMatrix_self v g _ (hg _)

theorem evalAt_chartNum (v : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) (r c : Fin n)
    (hc : evalAt g (chartMinor v c) ≠ 0) :
    evalAt g (chartNum v r c) = evalAt g (chartPoly v) * chartMatrix v g r c := by
  classical
  rw [chartNum, chartPoly, map_mul, map_prod, map_prod, chartMatrix_apply,
    ← Finset.mul_prod_erase Finset.univ (fun k => evalAt g (chartMinor v k)) (Finset.mem_univ c)]
  field_simp

theorem chartBeta_det_isUnit (v : Equiv.Perm (Fin n)) (g : GL (Fin n) ℂ)
    (hg : ∀ c, evalAt (g : Matrix (Fin n) (Fin n) ℂ) (chartMinor v c) ≠ 0) :
    IsUnit (chartBeta v g).det := by
  refine isUnit_iff_ne_zero.mpr fun h => det_chartMatrix_ne_zero v g hg ?_
  rw [chartMatrix, Matrix.det_mul, h, mul_zero]

/-! ### Homogenization -/

theorem exists_homogenize_poly (v : Equiv.Perm (Fin n)) (r : MatrixPolynomial n) :
    ∃ (K : ℕ) (a : MatrixPolynomial n), a ∈ minorSpan (K • onesShape n) ∧
      ∀ g : Matrix (Fin n) (Fin n) ℂ, (∀ c, evalAt g (chartMinor v c) ≠ 0) →
        evalAt g a = evalAt g (chartPoly v) ^ K * evalAt (chartMatrix v g) r := by
  induction r using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, MvPolynomial.C a, ?_, fun g _ => by simp [evalAt]⟩
    rw [zero_smul, ← mul_one (MvPolynomial.C a), ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ a one_mem_minorSpan
  | add p q hp hq =>
    obtain ⟨K₁, a₁, ha₁, h₁⟩ := hp
    obtain ⟨K₂, a₂, ha₂, h₂⟩ := hq
    refine ⟨K₁ + K₂, a₁ * chartPoly v ^ K₂ + a₂ * chartPoly v ^ K₁, ?_, fun g hg => ?_⟩
    · rw [add_smul]
      refine Submodule.add_mem _ (mul_mem_minorSpan ha₁
        (pow_mem_minorSpan (chartPoly_mem_minorSpan v) K₂)) ?_
      rw [add_comm]
      exact mul_mem_minorSpan ha₂ (pow_mem_minorSpan (chartPoly_mem_minorSpan v) K₁)
    · rw [map_add, map_mul, map_mul, map_pow, map_pow, h₁ g hg, h₂ g hg, map_add]
      ring
  | mul_X p rc hp =>
    obtain ⟨K₁, a₁, ha₁, h₁⟩ := hp
    refine ⟨K₁ + 1, a₁ * chartNum v rc.1 rc.2, ?_, fun g hg => ?_⟩
    · rw [succ_nsmul]
      exact mul_mem_minorSpan ha₁ (chartNum_mem_minorSpan v rc.1 rc.2)
    · rw [map_mul, h₁ g hg, evalAt_chartNum v g rc.1 rc.2 (hg rc.2), map_mul, evalAt_X]
      ring

/-- `E_m = ∏_c D_c^{m_c}`, the extremal product of shape `m` in the chart. -/
def chartExtremal (v : Equiv.Perm (Fin n)) (m : ColumnShape n) : MatrixPolynomial n :=
  ∏ c, chartMinor v c ^ m c

theorem chartExtremal_mem_minorSpan (v : Equiv.Perm (Fin n)) (m : ColumnShape n) :
    chartExtremal v m ∈ minorSpan m := by
  have h := prod_mem_minorSpan Finset.univ (fun c => chartMinor v c ^ m c)
    (fun c => m c • Pi.single c 1)
    fun c _ => pow_mem_minorSpan (flagRowMinor_mem_minorSpan _ _) _
  have hm : ∑ c, m c • (Pi.single c 1 : ColumnShape n) = m := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  rwa [hm] at h

/-- **Homogenization on the big cell `G_v`.** A function `t ∈ 𝒪(GL_n)` semi-invariant of weight
`shapeWeight m` on a set `Z` is, on `Z`, of the form `a / f_v^K` with `a` in the
flag-minor algebra of shape `m + K·(1, …, 1)`; moreover `a` vanishes on `Z ∖ G_v`. -/
theorem exists_homogenization (v : Equiv.Perm (Fin n)) {Z : Set (GL (Fin n) ℂ)} {m : ColumnShape n}
    {t : GLCoord ℂ n} (ht : IsSemiInvOn Z (shapeWeightZ m) t) :
    ∃ (K : ℕ) (a : MatrixPolynomial n), a ∈ minorSpan (m + K • onesShape n) ∧
      ∀ g ∈ Z, evalAt (g : Matrix (Fin n) (Fin n) ℂ) a =
        evalAt (g : Matrix (Fin n) (Fin n) ℂ) (chartPoly v) ^ K * glEval g t := by
  obtain ⟨r, k, hrk⟩ := exists_mul_det_pow t
  obtain ⟨K, a₀, ha₀, h₀⟩ := exists_homogenize_poly v r
  refine ⟨K + 1, ((Equiv.Perm.sign v : ℂ) ^ k) • (chartExtremal v m * a₀ * chartPoly v), ?_,
    fun g hg => ?_⟩
  · refine Submodule.smul_mem _ _ ?_
    rw [succ_nsmul, ← add_assoc]
    exact mul_mem_minorSpan (mul_mem_minorSpan (chartExtremal_mem_minorSpan v m) ha₀)
      (chartPoly_mem_minorSpan v)
  by_cases hgv : ∀ c, evalAt (g : Matrix (Fin n) (Fin n) ℂ) (chartMinor v c) ≠ 0
  · -- `g = L(g) β(g)⁻¹` with `L(g) ∈ Z`
    obtain ⟨β, hβdef⟩ : ∃ β : GL (Fin n) ℂ, (β : Matrix (Fin n) (Fin n) ℂ) = chartBeta v g :=
      ⟨unitOfDet (chartBeta v g) (chartBeta_det_isUnit v g hgv), coe_unitOfDet _ _⟩
    have hβ : IsBorel β := by
      unfold IsBorel
      rw [hβdef]
      exact chartBeta_isUpperTriangular v g
    have hL : ((g * β : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = chartMatrix v g := by
      rw [Units.val_mul, hβdef]
      rfl
    have hsemi := ht g hg β hβ
    rw [borelCharValue_shapeWeightZ, hβdef] at hsemi
    have hE := evalAt_mul_of_mem_minorSpan (chartExtremal_mem_minorSpan v m)
      (g : Matrix (Fin n) (Fin n) ℂ) (chartBeta v g) (chartBeta_isUpperTriangular v g)
    rw [show (g : Matrix (Fin n) (Fin n) ℂ) * chartBeta v g = chartMatrix v g from rfl] at hE
    have hE1 : evalAt (chartMatrix v g) (chartExtremal v m) = 1 := by
      rw [chartExtremal, map_prod]
      exact Finset.prod_eq_one fun c _ => by
        rw [map_pow, evalAt_chartMatrix_chartMinor v g hgv c, one_pow]
    rw [hE1] at hE
    -- the value of `t` at `L(g)`
    have hdet : glEval (g * β) t * (chartMatrix v g).det ^ k = evalAt (chartMatrix v g) r := by
      have := congrArg (glEval (g * β)) hrk
      rwa [map_mul, glEval_algebraMap_eq_evalAt, glEval_algebraMap_eq_evalAt, map_pow,
          evalAt_detPoly, hL] at this
    have hsign := det_chartMatrix v g hgv
    have hevL : glEval (g * β) t = (Equiv.Perm.sign v : ℂ) ^ k * evalAt (chartMatrix v g) r := by
      rw [← hdet, mul_comm (glEval (g * β) t), ← mul_assoc, ← mul_pow, hsign, one_pow, one_mul]
    have key : glEval g t = evalAt (g : Matrix _ _ ℂ) (chartExtremal v m) * glEval (g * β) t := by
      rw [hsemi, ← mul_assoc, mul_comm (evalAt _ _), ← hE, one_mul]
    rw [map_smul, map_mul, map_mul, smul_eq_mul, h₀ _ hgv, pow_succ, key, hevL]
    ring
  · push Not at hgv
    obtain ⟨c, hc⟩ := hgv
    have hf : evalAt (g : Matrix (Fin n) (Fin n) ℂ) (chartPoly v) = 0 := by
      rw [chartPoly, map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ c) hc
    rw [map_smul, map_mul, hf, mul_zero, smul_zero, zero_pow (Nat.succ_ne_zero K), zero_mul]

end

end FlagVarieties.PointModel.Complex
