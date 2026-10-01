import Schubert.GLRep.Weyl.Vandermonde
import Schubert.GLRep.Weyl.Dominance
import Mathlib.Tactic.LinearCombination

/-!
# The Laplacian eigen-equation for `a_δ χ`

Let `χ` be a Laurent polynomial in `n` variables over a field, and suppose that there are Laurent
polynomials `U_{ab}`, one for each pair `a < b`, with

* `c χ = D χ + ∑_{a<b} (θ_a − θ_b) χ + 2 ∑_{a<b} U_{ab}`,
* `U_{ab} (x_a − x_b) = x_b (θ_a − θ_b) χ` for every `a < b`,
* `∑_k θ_k χ = d χ`.

These are **Freudenthal's formula** and the **root-string recursion** for the character `χ` of a
`gl_n`-module on which the Casimir element acts by `c` and the identity matrix by `d`; the
`U_{ab}` record the traces of `E_{ba} E_{ab}` on the weight spaces. Then the product `a_δ χ` with
the staircase alternant `a_δ = ∏_{a<b} (x_a − x_b)` is an eigenvector of the Laplacian
`D = ∑_k θ_k²` (`GLRep.LaurentPoly.laplace_alternant_staircase_mul`):

`D(a_δ χ) = (c + (n − 1) d + |δ|²) a_δ χ`.

## Main definitions

* `GLRep.LaurentPoly.var`: the variable `x_i`.
* `GLRep.LaurentPoly.staircase`: `δ = (n − 1, …, 1, 0)`.

## Main results

* `GLRep.LaurentPoly.alternant_staircase`: `a_δ = ∏_{a<b} (x_a − x_b)`.
* `GLRep.LaurentPoly.laplace_alternant_staircase_mul`: the eigen-equation.
-/

namespace GLRep

open Finset

noncomputable section

/-- Over the pairs `a < b`, each index occurs `n − 1` times, as `a` or as `b`. -/
theorem sum_posPairs_add {M : Type*} [AddCommMonoid M] {n : ℕ} (f : Fin n → M) :
    ∑ p ∈ posPairs n, (f p.1 + f p.2) = (n - 1) • ∑ k, f k := by
  classical
  have h1 : ∑ p ∈ posPairs n, f p.1 = ∑ a, (Ioi a).card • f a := by
    rw [posPairs, sum_filter, ← univ_product_univ, sum_product]
    refine sum_congr rfl fun a _ => ?_
    rw [← sum_filter]
    dsimp only
    rw [sum_const]
    congr 2
    ext b
    simp
  have h2 : ∑ p ∈ posPairs n, f p.2 = ∑ b, (Iio b).card • f b := by
    rw [posPairs, sum_filter, ← univ_product_univ, sum_product_right]
    refine sum_congr rfl fun b _ => ?_
    rw [← sum_filter]
    dsimp only
    rw [sum_const]
    congr 2
    ext a
    simp
  rw [sum_add_distrib, h1, h2, ← sum_add_distrib, smul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [← add_smul, Fin.card_Ioi, Fin.card_Iio]
  congr 1
  have := k.isLt
  omega

namespace LaurentPoly

variable {K : Type*} [Field K] {n : ℕ}

/-- The variable `x_i`. -/
def var (i : Fin n) : LaurentPoly K n := AddMonoidAlgebra.single (Pi.single i 1) 1

theorem euler_var (k i : Fin n) :
    euler k (var i : LaurentPoly K n) = if k = i then var i else 0 := by
  rw [var, euler_single]
  split_ifs with hki
  · subst hki
    simp
  · simp [hki]

theorem sum_euler_var_mul (i : Fin n) (g : Fin n → LaurentPoly K n) :
    ∑ k, euler k (var i : LaurentPoly K n) * g k = var i * g i := by
  simp only [euler_var, ite_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]

/-- The staircase `δ = (n − 1, …, 1, 0)`. -/
def staircase (n : ℕ) : Fin n → ℤ := fun j => (n : ℤ) - 1 - j

theorem staircase_strictAnti (n : ℕ) : StrictAnti (staircase n) := fun i j hij => by
  have : (i : ℤ) < j := by exact_mod_cast hij
  simp only [staircase]
  omega

/-- `a_δ = ∏_{a<b} (x_a − x_b)`. -/
theorem alternant_staircase :
    alternant (staircase n) = ∏ p ∈ posPairs n, ((var p.1 : LaurentPoly K n) - var p.2) := by
  have h := congrArg (ofPoly K n) (alternant_staircase_eq_vandermonde K n)
  rw [ofPoly_alternant, vandermonde, map_prod] at h
  convert h using 2
  · funext j
    simp only [staircase]
    have := j.isLt
    omega
  · rw [map_sub, ofPoly_X, ofPoly_X]
    rfl

/-- The Euler operators on a finite product. -/
theorem euler_prod {ι : Type*} [DecidableEq ι] (k : Fin n) (s : Finset ι)
    (f : ι → LaurentPoly K n) :
    euler k (∏ i ∈ s, f i) = ∑ i ∈ s, euler k (f i) * ∏ j ∈ s.erase i, f j := by
  induction s using Finset.induction_on with
  | empty =>
    rw [prod_empty, sum_empty, show (1 : LaurentPoly K n) = AddMonoidAlgebra.single 0 1 from rfl,
      euler_single]
    simp
  | insert a s ha ih =>
    rw [prod_insert ha, euler_mul, ih, sum_insert ha, erase_insert ha, mul_sum]
    have hs : ∀ i ∈ s, euler k (f i) * ∏ j ∈ (insert a s).erase i, f j =
        f a * (euler k (f i) * ∏ j ∈ s.erase i, f j) := by
      intro i hi
      have hai : a ≠ i := fun h => ha (h ▸ hi)
      rw [erase_insert_of_ne hai, prod_insert (fun h => ha (mem_of_mem_erase h))]
      ring
    rw [sum_congr rfl hs]

/-- **The Laplacian eigen-equation for `a_δ χ`.** -/
theorem laplace_alternant_staircase_mul (χ : LaurentPoly K n) (U : Fin n × Fin n → LaurentPoly K n)
    (c d : K)
    (hF : c • χ = laplace χ + ∑ p ∈ posPairs n, (euler p.1 χ - euler p.2 χ) +
      2 * ∑ p ∈ posPairs n, U p)
    (hR : ∀ p ∈ posPairs n, U p * (var p.1 - var p.2) = var p.2 * (euler p.1 χ - euler p.2 χ))
    (hE : ∑ k, euler k χ = d • χ) :
    laplace (alternant (staircase n) * χ) =
      (c + ((n - 1 : ℕ) : K) * d + (normSq (staircase n) : K)) • (alternant (staircase n) * χ) := by
  classical
  set V : LaurentPoly K n := alternant (staircase n) with hV_def
  set P := posPairs n
  -- the cofactors of the Vandermonde product
  let W : Fin n × Fin n → LaurentPoly K n := fun p => ∏ q ∈ P.erase p, (var q.1 - var q.2)
  have hVW : ∀ p ∈ P, V = (var p.1 - var p.2) * W p := fun p hp => by
    rw [hV_def, alternant_staircase, ← mul_prod_erase P _ hp]
  -- `∑_k θ_k(V) θ_k(χ) = V ∑_p U_p + V ∑_p θ_{p.1} χ`
  have hS : ∑ k, euler k V * euler k χ =
      V * ∑ p ∈ P, U p + V * ∑ p ∈ P, euler p.1 χ := by
    have hθ : ∀ k, euler k V = ∑ p ∈ P, (euler k (var p.1) - euler k (var p.2)) * W p := by
      intro k
      rw [hV_def, alternant_staircase, euler_prod]
      simp only [map_sub]
      rfl
    simp only [hθ, sum_mul]
    rw [sum_comm]
    simp only [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun p hp => ?_
    have hrow : ∑ k, (euler k (var p.1) - euler k (var p.2)) * W p * euler k χ =
        W p * (var p.1 * euler p.1 χ - var p.2 * euler p.2 χ) := by
      simp only [sub_mul, sum_sub_distrib, mul_assoc]
      rw [sum_euler_var_mul p.1 (fun k => W p * euler k χ),
        sum_euler_var_mul p.2 (fun k => W p * euler k χ)]
      ring
    rw [hrow, hVW p hp]
    linear_combination (-(W p)) * hR p hp
  have hD : laplace V = (normSq (staircase n) : K) • V := laplace_alternant _
  have hAB : ∑ p ∈ P, euler p.1 χ + ∑ p ∈ P, euler p.2 χ =
      algebraMap K (LaurentPoly K n) ((n - 1 : ℕ) : K) * (algebraMap K _ d * χ) := by
    rw [← sum_add_distrib, sum_posPairs_add (fun k => euler k χ), hE, ← Nat.cast_smul_eq_nsmul K,
      Algebra.smul_def, Algebra.smul_def]
  have hL := laplace_mul V χ
  rw [hD] at hL
  rw [sum_sub_distrib] at hF
  rw [Algebra.smul_def] at hF hL ⊢
  rw [hS] at hL
  simp only [map_add, map_mul]
  linear_combination hL - V * hF + V * hAB

end LaurentPoly

end

end GLRep
