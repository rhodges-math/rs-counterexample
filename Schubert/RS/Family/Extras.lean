import Schubert.RS.Family.Main
import Schubert.RS.Family.Narayana
import Mathlib.Order.Bounds.Defs
import Mathlib.Tactic.IntervalCases

/-!
# Theorem 1.1: the Narayana form and the first negative cases

* (1.6) in both displayed forms: the coefficient of `𝒜_c` in `κ_a κ_b` equals
  `((p+q-1)/(pq))·C(p+q-2, p-1)²·(2 - (p-2)(q-2)) = N(p+q-1, p)·(2 - (p-2)(q-2))`,
  where `N` is the Narayana number (`atomCoefficient_eq_narayana`, `atomCoefficient_eq_paper`).
* The members `(p, q) = (3, 5)`, `(4, 4)`, `(5, 3)` live in `28` variables and have
  coefficients `-105`, `-350`, `-105` for every scale `δ ≥ 8`.
* A negative coefficient forces `p + q ≥ 8`; at `p + q = 8` exactly the three members above
  are negative. Hence the first negative cases within the family occur in `28` variables
  (`isLeast_rank_of_negative`).
-/

namespace Schubert.RS.Family
noncomputable section

theorem Parameters.m_eq (P : Parameters) : P.m = P.p + P.q - 1 := rfl

theorem Parameters.rank_eq (P : Parameters) : P.rank = 4 * (P.p + P.q - 1) := rfl

/-- (1.6), Narayana form: the family coefficient is `N(p+q-1, p)·(2 - (p-2)(q-2))`. -/
theorem atomCoefficient_eq_narayana (P : Parameters) :
    atomCoefficient (key (a P) * key (b P)) (c P) =
      (narayana (P.p + P.q - 1) P.p : ℤ) * (2 - ((P.p : ℤ) - 2) * ((P.q : ℤ) - 2)) := by
  rw [atomCoefficient_eq]
  exact coefficientValue_eq_narayana P.p_pos P.q_pos P.pq_eq

/-- (1.6) exactly as displayed, in the rationals: both the binomial and the Narayana
expression. -/
theorem atomCoefficient_eq_paper (P : Parameters) :
    (atomCoefficient (key (a P) * key (b P)) (c P) : ℚ) =
        ((P.p + P.q - 1 : ℕ) : ℚ) / ((P.p : ℚ) * P.q) *
          ((P.p + P.q - 2).choose (P.p - 1) : ℚ) ^ 2 * (2 - ((P.p : ℚ) - 2) * ((P.q : ℚ) - 2)) ∧
    (atomCoefficient (key (a P) * key (b P)) (c P) : ℚ) =
        (narayana (P.p + P.q - 1) P.p : ℚ) * (2 - ((P.p : ℚ) - 2) * ((P.q : ℚ) - 2)) := by
  constructor
  · rw [atomCoefficient_factorization]
    have hm : P.m - 1 = P.p + P.q - 2 := by rw [Parameters.m_eq]; omega
    rw [hm, Parameters.m_eq]
  · rw [atomCoefficient_eq_narayana]
    push_cast
    ring

/-- The family member `(p, q) = (3, 5)` at scale `δ ≥ 8`. -/
def threeFive (δ : ℕ) (hδ : 8 ≤ δ) : Parameters := ⟨3, 5, δ, by decide, by decide, by omega⟩

/-- The family member `(p, q) = (4, 4)` at scale `δ ≥ 8`. -/
def fourFour (δ : ℕ) (hδ : 8 ≤ δ) : Parameters := ⟨4, 4, δ, by decide, by decide, by omega⟩

/-- The family member `(p, q) = (5, 3)` at scale `δ ≥ 8`. -/
def fiveThree (δ : ℕ) (hδ : 8 ≤ δ) : Parameters := ⟨5, 3, δ, by decide, by decide, by omega⟩

theorem threeFive_rank (δ : ℕ) (hδ : 8 ≤ δ) : (threeFive δ hδ).rank = 28 := rfl

theorem fourFour_rank (δ : ℕ) (hδ : 8 ≤ δ) : (fourFour δ hδ).rank = 28 := rfl

theorem fiveThree_rank (δ : ℕ) (hδ : 8 ≤ δ) : (fiveThree δ hδ).rank = 28 := rfl

/-- `(p, q) = (3, 5)`: the coefficient is `-105` in `28` variables for every `δ ≥ 8`. -/
theorem atomCoefficient_threeFive (δ : ℕ) (hδ : 8 ≤ δ) :
    atomCoefficient (key (a (threeFive δ hδ)) * key (b (threeFive δ hδ)))
      (c (threeFive δ hδ)) = -105 := by
  rw [atomCoefficient_eq]
  show 2 * ((Nat.choose 7 2 : ℕ) : ℤ) * ((Nat.choose 7 3 : ℕ) : ℤ) -
    ((7 : ℕ) : ℤ) * ((Nat.choose 6 2 : ℕ) : ℤ) ^ 2 = -105
  decide

/-- `(p, q) = (4, 4)`: the coefficient is `-350` in `28` variables for every `δ ≥ 8`. -/
theorem atomCoefficient_fourFour (δ : ℕ) (hδ : 8 ≤ δ) :
    atomCoefficient (key (a (fourFour δ hδ)) * key (b (fourFour δ hδ)))
      (c (fourFour δ hδ)) = -350 := by
  rw [atomCoefficient_eq]
  show 2 * ((Nat.choose 7 3 : ℕ) : ℤ) * ((Nat.choose 7 4 : ℕ) : ℤ) -
    ((7 : ℕ) : ℤ) * ((Nat.choose 6 3 : ℕ) : ℤ) ^ 2 = -350
  decide

/-- `(p, q) = (5, 3)`: the coefficient is `-105` in `28` variables for every `δ ≥ 8`. -/
theorem atomCoefficient_fiveThree (δ : ℕ) (hδ : 8 ≤ δ) :
    atomCoefficient (key (a (fiveThree δ hδ)) * key (b (fiveThree δ hδ)))
      (c (fiveThree δ hδ)) = -105 := by
  rw [atomCoefficient_eq]
  show 2 * ((Nat.choose 7 4 : ℕ) : ℤ) * ((Nat.choose 7 5 : ℕ) : ℤ) -
    ((7 : ℕ) : ℤ) * ((Nat.choose 6 4 : ℕ) : ℤ) ^ 2 = -105
  decide

/-- A negative family coefficient forces `p + q ≥ 8`. -/
theorem eight_le_of_atomCoefficient_neg (P : Parameters)
    (h : atomCoefficient (key (a P) * key (b P)) (c P) < 0) : 8 ≤ P.p + P.q := by
  rw [atomCoefficient_neg_iff] at h
  obtain ⟨p, q, K, hp, hq, hK⟩ := P
  simp only at h ⊢
  by_contra h8
  have hp' : p ≤ 6 := by omega
  have hq' : q ≤ 6 := by omega
  interval_cases p <;> interval_cases q <;> omega

/-- At `p + q = 8` the negative members are exactly `(3, 5)`, `(4, 4)` and `(5, 3)`. -/
theorem atomCoefficient_neg_iff_of_sum_eight (P : Parameters) (h8 : P.p + P.q = 8) :
    atomCoefficient (key (a P) * key (b P)) (c P) < 0 ↔
      (P.p = 3 ∧ P.q = 5) ∨ (P.p = 4 ∧ P.q = 4) ∨ (P.p = 5 ∧ P.q = 3) := by
  rw [atomCoefficient_neg_iff]
  obtain ⟨p, q, K, hp, hq, hK⟩ := P
  simp only at h8 ⊢
  have hp' : p ≤ 7 := by omega
  obtain rfl : q = 8 - p := by omega
  interval_cases p <;> decide

/-- The first negative cases within the family occur in `28` variables: `28` is the least
rank `4(p+q-1)` of a family member with a negative coefficient. -/
theorem isLeast_rank_of_negative :
    IsLeast {r : ℕ | ∃ P : Parameters, P.rank = r ∧
      atomCoefficient (key (a P) * key (b P)) (c P) < 0} 28 := by
  refine ⟨⟨threeFive 8 le_rfl, threeFive_rank 8 le_rfl, ?_⟩, ?_⟩
  · rw [atomCoefficient_threeFive]
    decide
  · rintro r ⟨P, rfl, hP⟩
    have h8 := eight_le_of_atomCoefficient_neg P hP
    rw [Parameters.rank_eq]
    omega

end
end Schubert.RS.Family
