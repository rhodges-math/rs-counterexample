import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Basic solutions of linear systems in standard form

A nonnegative solution `w` of `M w = c` can be replaced by one whose support columns are linearly
independent, without increasing a nonnegative linear objective `f · w`
(`LinearProgramming.exists_indepSupport`). If the support columns of `w` are dependent, a nonzero
kernel vector `d` supported there exists. It can be oriented so that `f · d ≤ 0` and `d` has a
negative entry. Then `w + t d` for the largest admissible `t ≥ 0` is again a nonnegative solution,
with a smaller support and a value of `f` that is no larger. This is the argument for basic
solutions and the fundamental theorem of linear programming (Schrijver, *Theory of Linear and
Integer Programming*, §7.8; compare Carathéodory's theorem).

## Main definitions

* `LinearProgramming.IndepSupport M w`: the columns of `M` on the support of `w` are linearly
  independent.

## Main results

* `LinearProgramming.exists_indepSupport`: every nonnegative solution can be replaced by a
  nonnegative solution with linearly independent support columns and no larger objective.
-/

namespace LinearProgramming

open Matrix

variable {ρ ι : Type*} [Fintype ι]

/-- The support of `w`. -/
def supp (w : ι → ℚ) : Finset ι := Finset.univ.filter fun j => w j ≠ 0

theorem mem_supp {w : ι → ℚ} {j : ι} : j ∈ supp w ↔ w j ≠ 0 := by
  simp [supp]

/-- The columns of `M` on the support of `w` are linearly independent. -/
def IndepSupport (M : Matrix ρ ι ℚ) (w : ι → ℚ) : Prop :=
  LinearIndependent ℚ fun j : {j // w j ≠ 0} => fun i => M i j

/-- Dependent support columns give a nonzero kernel vector supported on the support. -/
theorem exists_kernel_of_not_indepSupport {M : Matrix ρ ι ℚ} {w : ι → ℚ}
    (h : ¬ IndepSupport M w) :
    ∃ d : ι → ℚ, M *ᵥ d = 0 ∧ (∀ j, d j ≠ 0 → w j ≠ 0) ∧ ∃ j, d j ≠ 0 := by
  classical
  obtain ⟨g, hg, j, hj⟩ := Fintype.not_linearIndependent_iff.mp h
  refine ⟨fun k => if hk : w k ≠ 0 then g ⟨k, hk⟩ else 0, ?_, fun k hk => ?_, j, ?_⟩
  · funext i
    have hi := congrFun hg i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
    simp only [mulVec, dotProduct, Pi.zero_apply]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun k => w k ≠ 0)]
    have h2 : ∑ x : {k // ¬ (w k ≠ 0)},
        M i x * (if hk : w x ≠ 0 then g ⟨x, hk⟩ else 0) = 0 :=
      Finset.sum_eq_zero fun x _ => by rw [dite_eq_right x.2, mul_zero]
    rw [h2, add_zero]
    exact (Finset.sum_congr rfl fun x _ => by rw [dite_eq_left x.2, mul_comm]).trans hi
  · by_contra hw
    simp [hw] at hk
  · simpa [j.2] using hj

/-- A kernel vector supported on the support of `w`, with `f · e ≤ 0` and a negative entry. -/
theorem exists_descent {M : Matrix ρ ι ℚ} {w f : ι → ℚ} (hf : ∀ j, 0 ≤ f j)
    (h : ¬ IndepSupport M w) :
    ∃ e : ι → ℚ, M *ᵥ e = 0 ∧ (∀ j, e j ≠ 0 → w j ≠ 0) ∧ f ⬝ᵥ e ≤ 0 ∧ ∃ j, e j < 0 := by
  obtain ⟨d, hd, hsupp, j, hj⟩ := exists_kernel_of_not_indepSupport h
  -- orient `d` so that the objective does not increase
  obtain ⟨d₁, hd₁, hsupp₁, hf₁, j₁, hj₁⟩ : ∃ d₁ : ι → ℚ, M *ᵥ d₁ = 0 ∧
      (∀ j, d₁ j ≠ 0 → w j ≠ 0) ∧ f ⬝ᵥ d₁ ≤ 0 ∧ ∃ j, d₁ j ≠ 0 := by
    by_cases hfd : f ⬝ᵥ d ≤ 0
    · exact ⟨d, hd, hsupp, hfd, j, hj⟩
    · refine ⟨-d, by rw [mulVec_neg, hd, neg_zero], fun k hk => hsupp k (by simpa using hk),
        by rw [dotProduct_neg]; linarith, j, by simpa using hj⟩
  by_cases hneg : ∃ k, d₁ k < 0
  · exact ⟨d₁, hd₁, hsupp₁, hf₁, hneg⟩
  · push Not at hneg
    have hpos : 0 ≤ f ⬝ᵥ d₁ :=
      Finset.sum_nonneg fun k _ => mul_nonneg (hf k) (hneg k)
    refine ⟨-d₁, by rw [mulVec_neg, hd₁, neg_zero], fun k hk => hsupp₁ k (by simpa using hk),
      by rw [dotProduct_neg]; linarith, j₁, ?_⟩
    have := lt_of_le_of_ne (hneg j₁) (Ne.symm hj₁)
    simpa using this

/-- One step of support reduction: a nonnegative solution with dependent support columns can be
replaced by one with a strictly smaller support and no larger objective. -/
theorem exists_reduce {M : Matrix ρ ι ℚ} {w f : ι → ℚ} {c' : ρ → ℚ} (hf : ∀ j, 0 ≤ f j)
    (hw : ∀ j, 0 ≤ w j) (hMw : M *ᵥ w = c') (h : ¬ IndepSupport M w) :
    ∃ w' : ι → ℚ, (∀ j, 0 ≤ w' j) ∧ M *ᵥ w' = c' ∧ f ⬝ᵥ w' ≤ f ⬝ᵥ w ∧
      (supp w').card < (supp w).card := by
  classical
  obtain ⟨e, he, hsupp, hfe, j, hj⟩ := exists_descent hf h
  set N := Finset.univ.filter fun k => e k < 0 with hN
  have hNne : N.Nonempty := ⟨j, by simp [hN, hj]⟩
  obtain ⟨k₀, hk₀N, hk₀⟩ := N.exists_min_image (fun k => w k / -e k) hNne
  have hek₀ : e k₀ < 0 := by simpa [hN] using hk₀N
  set t := w k₀ / -e k₀ with ht
  have ht0 : 0 ≤ t := div_nonneg (hw k₀) (by linarith)
  refine ⟨w + t • e, fun k => ?_, ?_, ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hek : e k < 0
    · have hle : t ≤ w k / -e k := hk₀ k (by simp [hN, hek])
      rw [le_div_iff₀ (by linarith)] at hle
      linarith
    · push Not at hek
      nlinarith [hw k]
  · rw [mulVec_add, mulVec_smul, he, smul_zero, add_zero, hMw]
  · rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    nlinarith
  · apply Finset.card_lt_card
    refine ⟨fun k hk => ?_, fun hsub => ?_⟩
    · rw [mem_supp] at hk ⊢
      intro hwk
      apply hk
      have hek : e k = 0 := by
        by_contra hne
        exact hsupp k hne hwk
      simp [hwk, hek]
    · have hk₀w : w k₀ ≠ 0 := hsupp k₀ (ne_of_lt hek₀)
      have := hsub (mem_supp.mpr hk₀w)
      rw [mem_supp] at this
      apply this
      have he0 : e k₀ ≠ 0 := ne_of_lt hek₀
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ht]
      field_simp
      ring

/-- **Basic solutions.** Every nonnegative solution of `M w = c` can be replaced by a nonnegative
solution whose support columns are linearly independent and whose value of the nonnegative
objective `f` is no larger. -/
theorem exists_indepSupport (M : Matrix ρ ι ℚ) (c : ρ → ℚ) {f : ι → ℚ} (hf : ∀ j, 0 ≤ f j)
    {w : ι → ℚ} (hw : ∀ j, 0 ≤ w j) (hMw : M *ᵥ w = c) :
    ∃ w' : ι → ℚ, (∀ j, 0 ≤ w' j) ∧ M *ᵥ w' = c ∧ f ⬝ᵥ w' ≤ f ⬝ᵥ w ∧ IndepSupport M w' := by
  induction hcard : (supp w).card using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    by_cases hind : IndepSupport M w
    · exact ⟨w, hw, hMw, le_rfl, hind⟩
    · obtain ⟨w₁, hw₁, hMw₁, hf₁, hcard₁⟩ := exists_reduce hf hw hMw hind
      obtain ⟨w', hw', hMw', hf', hind'⟩ := ih _ (hcard ▸ hcard₁) hw₁ hMw₁ rfl
      exact ⟨w', hw', hMw', hf'.trans hf₁, hind'⟩

end LinearProgramming
