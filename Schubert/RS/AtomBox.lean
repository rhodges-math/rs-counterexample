import Schubert.RS.Keys

/-! Integral atoms preserve a coordinatewise exponent box. This elementary
operator fact is independent of the three representation-theoretic inputs. -/

namespace Schubert.RS
noncomputable section
open FinPermutation Schubert
variable {n : ℕ}

def exponentBox (n w : ℕ) : Submodule ℤ (Polynomial n) where
  carrier:={f | ∀ d,MvPolynomial.coeff d f≠0 → ∀ i,d i≤w}
  zero_mem':=by simp
  add_mem':=by
    intro f g hf hg d hd i
    by_cases h : MvPolynomial.coeff d f=0
    · apply hg d
      intro he
      simp [h,he] at hd
    · exact hf d h i
  smul_mem':=by
    intro z f hf d hd i
    apply hf d
    intro he
    change MvPolynomial.coeff d (z • f)≠0 at hd
    rw [MvPolynomial.coeff_smul,he,smul_zero] at hd
    exact hd rfl

theorem mem_exponentBox (w : ℕ) (f : Polynomial n) :
    f∈exponentBox n w ↔ ∀ d,MvPolynomial.coeff d f≠0 → ∀ i,d i≤w := Iff.rfl

theorem monomial_mem_exponentBox (w : ℕ) (d : Fin n →₀ ℕ) (z : ℤ) (hd : ∀ i,d i≤w) :
    MvPolynomial.monomial d z∈exponentBox n w := by
  intro e he i
  by_cases h : d=e
  · subst e
    exact hd i
  · simp [MvPolynomial.coeff_monomial,h] at he

def atomOperatorLinearMap (i : AdjacentPosition n) : Polynomial n →ₗ[ℤ] Polynomial n where
  toFun:=atomOperator i
  map_add' f g:=by simp only [atomOperator,isobaric_add]; abel
  map_smul' z f:=by simp only [atomOperator,isobaric_smul,smul_sub]; rfl

theorem atomOperator_monomial_mem_exponentBox (w : ℕ) (i : AdjacentPosition n)
    (d : Fin n →₀ ℕ) (z : ℤ) (hd : ∀ j,d j≤w) :
    atomOperator i (MvPolynomial.monomial d z)∈exponentBox n w := by
  rw [atomOperator_eq,adjacentDividedDifference_monomial,mul_smul_comm]
  apply (exponentBox n w).smul_mem
  unfold monomialDividedDifference
  split_ifs with hr hl
  · rw [Finset.mul_sum]
    apply (exponentBox n w).sum_mem
    intro k hk
    have hk':=Finset.mem_range.mp hk
    rw [X_right_mul_replaceAdjacentExponents]
    apply monomial_mem_exponentBox
    intro j
    by_cases h₁ : j=i.left
    · subst j
      rw [replaceAdjacentExponents_left]
      have h:=hd i.left
      omega
    by_cases h₂ : j=i.right
    · subst j
      rw [replaceAdjacentExponents_right]
      have h:=hd i.left
      omega
    · rw [replaceAdjacentExponents_of_ne _ _ _ _ _ h₁ h₂]
      exact hd j
  · rw [mul_neg,Finset.mul_sum]
    apply (exponentBox n w).neg_mem
    apply (exponentBox n w).sum_mem
    intro k hk
    have hk':=Finset.mem_range.mp hk
    rw [X_right_mul_replaceAdjacentExponents]
    apply monomial_mem_exponentBox
    intro j
    by_cases h₁ : j=i.left
    · subst j
      rw [replaceAdjacentExponents_left]
      have h:=hd i.right
      omega
    by_cases h₂ : j=i.right
    · subst j
      rw [replaceAdjacentExponents_right]
      have h:=hd i.right
      omega
    · rw [replaceAdjacentExponents_of_ne _ _ _ _ _ h₁ h₂]
      exact hd j
  · simp

theorem atomOperator_mem_exponentBox (w : ℕ) (i : AdjacentPosition n)
    (f : Polynomial n) (hf : f∈exponentBox n w) : atomOperator i f∈exponentBox n w := by
  have he : atomOperator i f=∑ d ∈ f.support,atomOperator i (MvPolynomial.monomial d (MvPolynomial.coeff d f)) := by
    change atomOperatorLinearMap i f=_
    conv_lhs => rw [f.as_sum]
    exact map_sum (atomOperatorLinearMap i) _ _
  rw [he]
  apply (exponentBox n w).sum_mem
  intro d hd
  exact atomOperator_monomial_mem_exponentBox w i d _
    (hf d (MvPolynomial.mem_support_iff.mp hd))

theorem atom_mem_exponentBox (w : ℕ) (a : Composition n) (ha : ∀ i,a i≤w) :
    atom a∈exponentBox n w := by
  by_cases h : (ascentSet a).Nonempty
  · rw [atom_ascent a h]
    apply atomOperator_mem_exponentBox
    apply atom_mem_exponentBox
    intro i
    exact ha _
  · rw [atom_of_no_ascent a h]
    exact monomial_mem_exponentBox w _ 1 ha
termination_by sortingMeasure a
decreasing_by exact sortingMeasure_firstAscent a h

end
end Schubert.RS

