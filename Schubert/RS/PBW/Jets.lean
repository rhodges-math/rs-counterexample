import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Complex.Basic

/-! Vanishing-order estimates for polynomial differential operators. -/
namespace Schubert.RS.PBW
noncomputable section
open scoped BigOperators
open MvPolynomial

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def exponentDegree (e : σ →₀ ℕ) : ℕ := ∑ i, e i

@[simp] theorem exponentDegree_zero : exponentDegree (0 : σ →₀ ℕ) = 0 := by
  simp [exponentDegree]

@[simp] theorem exponentDegree_add (e f : σ →₀ ℕ) :
    exponentDegree (e + f) = exponentDegree e + exponentDegree f := by
  simp [exponentDegree, Finset.sum_add_distrib]

@[simp] theorem exponentDegree_single (i : σ) (k : ℕ) :
    exponentDegree (Finsupp.single i k) = k := by
  simp [exponentDegree, Finsupp.single_apply]

/-- All terms of degree strictly less than d vanish. -/
def jet (d : ℕ) : Submodule ℂ (MvPolynomial σ ℂ) where
  carrier := {p | ∀ e, exponentDegree e < d → coeff e p = 0}
  zero_mem' := by simp
  add_mem' := by intro p q hp hq e he; simp [hp e he, hq e he]
  smul_mem' := by intro c p hp e he; simp [hp e he]

theorem jet_antitone {d k : ℕ} (h : k ≤ d) : jet (σ := σ) d ≤ jet k := by
  intro p hp e he
  exact hp e (lt_of_lt_of_le he h)

theorem monomial_mem_jet (e : σ →₀ ℕ) (c : ℂ) :
    monomial e c ∈ jet (exponentDegree e) := by
  intro f hf
  rw [coeff_monomial]
  exact if_neg (by intro h; subst e; omega)

theorem pderiv_mem_jet (i : σ) {d : ℕ} {p : MvPolynomial σ ℂ}
    (hp : p ∈ jet (d+1)) : pderiv i p ∈ jet d := by
  intro e he
  rw [coeff_pderiv, hp (e + Finsupp.single i 1) (by simp; omega), zero_mul]

theorem X_mul_mem_jet (i : σ) {d : ℕ} {p : MvPolynomial σ ℂ}
    (hp : p ∈ jet d) : X i * p ∈ jet (d+1) := by
  intro e he
  by_cases hi : e i = 0
  · simp [coeff_X_mul', hi]
  · have hle : Finsupp.single i 1 ≤ e := by
      rw [Finsupp.single_le_iff]; omega
    have hdeg : exponentDegree (e - Finsupp.single i 1) + 1 = exponentDegree e := by
      have h := congrArg exponentDegree (tsub_add_cancel_of_le hle)
      simpa using h
    rw [coeff_X_mul']
    split_ifs with h
    · exact hp _ (by omega)
    · rfl

theorem X_pderiv_mem_jet (i j : σ) {d : ℕ} {p : MvPolynomial σ ℂ}
    (hp : p ∈ jet d) : X i * pderiv j p ∈ jet d := by
  cases d with
  | zero => intro e he; omega
  | succ d => exact X_mul_mem_jet i (pderiv_mem_jet j hp)

def differentialWord {ι : Type*} (D : ι → Module.End ℂ (MvPolynomial σ ℂ))
    (w : List ι) : Module.End ℂ (MvPolynomial σ ℂ) := (w.map D).prod

@[simp] theorem differentialWord_nil {ι : Type*}
    (D : ι → Module.End ℂ (MvPolynomial σ ℂ)) : differentialWord D [] = 1 := rfl

theorem differentialWord_cons {ι : Type*}
    (D : ι → Module.End ℂ (MvPolynomial σ ℂ)) (i : ι) (w : List ι) :
    differentialWord D (i :: w) = D i * differentialWord D w := rfl

theorem differentialWord_append {ι : Type*}
    (D : ι → Module.End ℂ (MvPolynomial σ ℂ)) (w v : List ι) :
    differentialWord D (w ++ v) = differentialWord D w * differentialWord D v := by
  simp [differentialWord]

theorem differentialWord_mem_jet {ι : Type*}
    (D : ι → Module.End ℂ (MvPolynomial σ ℂ))
    (hD : ∀ i d p, p ∈ jet (d+1) → D i p ∈ jet d)
    (w : List ι) (d : ℕ) {p : MvPolynomial σ ℂ}
    (hp : p ∈ jet (d + w.length)) : differentialWord D w p ∈ jet d := by
  induction w generalizing d with
  | nil => simpa using hp
  | cons i w ih =>
    rw [differentialWord_cons]
    exact hD i d _ (ih (d+1) (by simpa [Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hp))

theorem differentialWord_constant_zero {ι : Type*}
    (D : ι → Module.End ℂ (MvPolynomial σ ℂ))
    (hD : ∀ i d p, p ∈ jet (d+1) → D i p ∈ jet d)
    (w : List ι) {p : MvPolynomial σ ℂ} (hp : p ∈ jet (w.length+1)) :
    coeff 0 (differentialWord D w p) = 0 := by
  exact differentialWord_mem_jet D hD w 1
    (by simpa [Nat.add_comm] using hp) 0 (by simp)

/-- The principal part at the origin ignores all linear-coefficient terms. -/
theorem differentialWord_principal {ι : Type*}
    (D : ι → Module.End ℂ (MvPolynomial σ ℂ)) (index : ι → σ)
    (hD : ∀ i d p, p ∈ jet (d+1) → D i p ∈ jet d)
    (herror : ∀ i d p, p ∈ jet d → D i p - pderiv (index i) p ∈ jet d)
    (w : List ι) {p : MvPolynomial σ ℂ} (hp : p ∈ jet w.length) :
    coeff 0 (differentialWord D w p) =
      coeff 0 (differentialWord (fun i => (pderiv (index i)).toLinearMap) w p) := by
  induction w using List.reverseRecOn generalizing p with
  | nil => rfl
  | append_singleton w i ih =>
    have hz := differentialWord_constant_zero D hD w
      (herror i (w.length+1) p (by simpa using hp))
    rw [map_sub, coeff_sub] at hz
    have heq := sub_eq_zero.mp hz
    have hp' : pderiv (index i) p ∈ jet w.length :=
      pderiv_mem_jet _ (by simpa using hp)
    simpa [differentialWord_append, differentialWord, List.map_append,
      List.prod_append, Module.End.mul_apply] using heq.trans (ih hp')

end
end Schubert.RS.PBW
