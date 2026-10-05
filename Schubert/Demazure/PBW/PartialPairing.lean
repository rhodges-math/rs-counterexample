import Schubert.Demazure.PBW.Jets

/-! Constant partial derivatives separate monomials of equal total degree. -/
namespace Demazure.PBW
noncomputable section
open scoped BigOperators
open MvPolynomial

variable {σ ι : Type*} [Fintype σ] [DecidableEq σ]

/-- The exponent vector counting the occurrences of each `index i` in a word. -/
def wordExponent (index : ι → σ) (w : List ι) : σ →₀ ℕ :=
  (w.map fun i => Finsupp.single (index i) 1).sum

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem wordExponent_nil (index : ι → σ) : wordExponent index [] = 0 := rfl

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem wordExponent_cons (index : ι → σ) (i : ι) (w : List ι) :
    wordExponent index (i :: w) = Finsupp.single (index i) 1 + wordExponent index w := rfl

@[simp] theorem wordExponent_degree (index : ι → σ) (w : List ι) :
    exponentDegree (wordExponent index w) = w.length := by
  induction w with
  | nil => simp
  | cons i w ih => simp [ih, Nat.add_comm]

omit [Fintype σ] [DecidableEq σ] in
theorem wordExponent_apply_index [DecidableEq ι] [BEq ι] [LawfulBEq ι] (index : ι → σ)
    (hindex : Function.Injective index) (w : List ι) (i : ι) :
    wordExponent index w (index i) = w.count i := by
  induction w with
  | nil => simp
  | cons j w ih =>
    by_cases h : j = i
    · subst j; simp [ih, Nat.add_comm]
    · simp [ih, h, Ne.symm (hindex.ne h)]

omit [Fintype σ] [DecidableEq σ] in
/-- Each word of ordinary partials reads one coefficient, multiplied by a
nonzero positive-integer factor. This proves the needed factorial diagonal
without introducing a separate normalization into the PBW interface. -/
theorem partialWord_coefficient (index : ι → σ) (w : List ι) (e : σ →₀ ℕ) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ p : MvPolynomial σ ℂ,
      (differentialWord (fun i => (pderiv (index i)).toLinearMap) w p).coeff e =
        c * p.coeff (e + wordExponent index w) := by
  induction w generalizing e with
  | nil => exact ⟨1, one_ne_zero, by intro p; simp⟩
  | cons i w ih =>
    obtain ⟨c, hc, hcoeff⟩ := ih (e + Finsupp.single (index i) 1)
    have hn : (e (index i) : ℂ) + 1 ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero (e (index i))
    refine ⟨c * ((e (index i) : ℂ) + 1), mul_ne_zero hc hn, ?_⟩
    intro p
    rw [differentialWord_cons, Module.End.mul_apply]
    change (pderiv (index i) _).coeff e = _
    rw [coeff_pderiv, hcoeff, wordExponent_cons]
    rw [add_assoc]
    ring

omit [Fintype σ] [DecidableEq σ] in
theorem partialWord_constant (index : ι → σ) (w : List ι) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ p : MvPolynomial σ ℂ,
      (differentialWord (fun i => (pderiv (index i)).toLinearMap) w p).coeff 0 =
        c * p.coeff (wordExponent index w) := by
  simpa using partialWord_coefficient index w 0

end
end Demazure.PBW
