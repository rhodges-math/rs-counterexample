import Schubert.RS.Representation.StringFiltration

/-! The polynomial character calculation for completion of an arbitrary
terminal E-string. The representation-theoretic universal property is separate. -/

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation Schubert
open scoped BigOperators

def twoVariableStringCharacter {n : ℕ} (i : AdjacentPosition n) (d : ℕ) : RS.Polynomial n :=
  isobaric i (MvPolynomial.monomial (Finsupp.single i.left d) 1)

theorem twoVariableStringCharacter_sum {n : ℕ} (i : AdjacentPosition n) (d : ℕ) :
    twoVariableStringCharacter i d =
      ∑ k ∈ Finset.range (d+1),
        MvPolynomial.monomial (Finsupp.single i.left (d-k)+Finsupp.single i.right k) 1 := by
  classical
  rw [twoVariableStringCharacter,isobaric_monomial i _ (by simp [i.left_ne_right.symm])]
  simp only [Finsupp.single_eq_same,Finsupp.single_eq_of_ne i.left_ne_right.symm,
    Nat.sub_zero,zero_add]
  apply Finset.sum_congr rfl
  intro k hk
  apply congrArg (fun w : Fin n →₀ ℕ => MvPolynomial.monomial w (1:ℤ))
  ext j
  by_cases hl : j=i.left
  · subst j; simp [i.left_ne_right]
  by_cases hr : j=i.right
  · subst j; simp [i.left_ne_right.symm]
  simp [replaceAdjacentExponents_of_ne _ _ _ _ _ hl hr,hl,hr]

def partialStringCharacter {n : ℕ} (i : AdjacentPosition n) (a : Fin n →₀ ℕ) (d : ℕ) :
    RS.Polynomial n := twoVariableStringCharacter i d * MvPolynomial.monomial a 1

def completedStringCharacter {n : ℕ} (i : AdjacentPosition n) (a : Fin n →₀ ℕ) (d : ℕ) :
    RS.Polynomial n := twoVariableStringCharacter i d * isobaric i (MvPolynomial.monomial a 1)

theorem partialStringCharacter_sum {n : ℕ} (i : AdjacentPosition n) (a : Fin n →₀ ℕ) (d : ℕ) :
    partialStringCharacter i a d =
      ∑ k ∈ Finset.range (d+1),
        MvPolynomial.monomial (a+Finsupp.single i.left (d-k)+Finsupp.single i.right k) 1 := by
  rw [partialStringCharacter,twoVariableStringCharacter_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [MvPolynomial.monomial_mul,one_mul]
  apply congrArg (fun w : Fin n →₀ ℕ => MvPolynomial.monomial w (1:ℤ))
  abel

/-- The source string is a symmetric character times a dominant line, so
the isobaric operator acts only on the line factor. -/
theorem partialStringCharacter_isobaric {n : ℕ} (i : AdjacentPosition n)
    (a : Fin n →₀ ℕ) (d : ℕ) :
    isobaric i (partialStringCharacter i a d)=completedStringCharacter i a d :=
  isobaric_mul_of_symmetric i _ _ (swap_isobaric i _)

theorem completedStringCharacter_sum {n : ℕ} (i : AdjacentPosition n)
    (a : Fin n →₀ ℕ) (ha : a i.right≤a i.left) (d : ℕ) :
    completedStringCharacter i a d =
      ∑ k ∈ Finset.range (d+1), ∑ l ∈ Finset.range (a i.left-a i.right+1),
        MvPolynomial.monomial
          (Finsupp.single i.left (d-k)+Finsupp.single i.right k+
            replaceAdjacentExponents a i (a i.left-l) (a i.right+l)) 1 := by
  rw [completedStringCharacter,twoVariableStringCharacter_sum,isobaric_monomial i a ha,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [MvPolynomial.monomial_mul,one_mul]

end
end Schubert.RS.Representation
