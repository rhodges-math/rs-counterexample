import Schubert.RS.MatrixUnitNilpotence

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators

def matrixMonomialWeight {n : ℕ} (d : (Fin n × Fin n) →₀ ℕ) : Weight n :=
  fun i => (∑ j, d (i,j) : ℕ)

theorem matrixMonomialTorusScalar_eq_weight {n : ℕ}
    (d : (Fin n × Fin n) →₀ ℕ) (t : DiagonalTorus n) :
    matrixMonomialTorusScalar d t = integerWeightScalar (matrixMonomialWeight d) t := by
  change d.prod (fun rc k => (t rc.1 : ℂ)^k) = _
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),Fintype.prod_prod_type]
  simp only [integerWeightScalar,matrixMonomialWeight,zpow_natCast,
    Finset.prod_pow_eq_pow_sum]

theorem polynomialTorus_coeff_weight {n : ℕ} (t : DiagonalTorus n)
    (d : (Fin n × Fin n) →₀ ℕ) (p : MatrixPolynomial n) :
    MvPolynomial.coeff d (polynomialTorus n t p) =
      integerWeightScalar (matrixMonomialWeight d) t * MvPolynomial.coeff d p := by
  rw [polynomialTorus_coeff,matrixMonomialTorusScalar_eq_weight]

def polynomialWeightFilter {n : ℕ} (t : DiagonalTorus n) (v w : Weight n)
    (p : MatrixPolynomial n) : MatrixPolynomial n :=
  (integerWeightScalar v t-integerWeightScalar w t)⁻¹ •
    (polynomialTorus n t p-integerWeightScalar w t • p)

theorem polynomialWeightFilter_coeff {n : ℕ} (t : DiagonalTorus n) (v w : Weight n)
    (p : MatrixPolynomial n) (d : (Fin n × Fin n) →₀ ℕ) :
    MvPolynomial.coeff d (polynomialWeightFilter t v w p) =
      (integerWeightScalar v t-integerWeightScalar w t)⁻¹ *
        (integerWeightScalar (matrixMonomialWeight d) t-integerWeightScalar w t) *
          MvPolynomial.coeff d p := by
  simp only [polynomialWeightFilter,MvPolynomial.coeff_smul,MvPolynomial.coeff_sub,
    polynomialTorus_coeff_weight,smul_eq_mul]
  ring

theorem polynomialWeightFilter_support {n : ℕ} (t : DiagonalTorus n) (v : Weight n)
    (p : MatrixPolynomial n) (d : (Fin n × Fin n) →₀ ℕ) :
    (polynomialWeightFilter t v (matrixMonomialWeight d) p).support ⊆ p.support.erase d := by
  classical
  intro e he
  have hn := MvPolynomial.mem_support_iff.mp he
  rw [polynomialWeightFilter_coeff] at hn
  apply Finset.mem_erase.mpr
  constructor
  · intro h; subst e; simp at hn
  · apply MvPolynomial.mem_support_iff.mpr
    intro hz; simp [hz] at hn

theorem polynomialWeightFilter_remainder_support {n : ℕ} (t : DiagonalTorus n)
    (w : Weight n) (p : MatrixPolynomial n) (d : (Fin n × Fin n) →₀ ℕ)
    (hne : integerWeightScalar (matrixMonomialWeight d) t≠integerWeightScalar w t) :
    (p-polynomialWeightFilter t (matrixMonomialWeight d) w p).support ⊆ p.support.erase d := by
  classical
  intro e he
  have hn := MvPolynomial.mem_support_iff.mp he
  rw [MvPolynomial.coeff_sub,polynomialWeightFilter_coeff] at hn
  apply Finset.mem_erase.mpr
  constructor
  · intro h; subst e
    rw [inv_mul_cancel₀ (sub_ne_zero.mpr hne),one_mul,sub_self] at hn
    exact hn rfl
  · apply MvPolynomial.mem_support_iff.mpr
    intro hz; simp [hz] at hn

def polynomialWeightSpan {n : ℕ} (S : Submodule ℂ (MatrixPolynomial n)) :
    Submodule ℂ (MatrixPolynomial n) :=
  Submodule.span ℂ {p | p∈S ∧ ∃ v : Weight n,
    ∀ t, polynomialTorus n t p=integerWeightScalar v t • p}

/-- A full-torus-stable polynomial subspace is spanned by its actual integral
weight vectors. The proof splits finite monomial support, so requires neither
semisimplicity nor a character formula. -/
theorem mem_polynomialWeightSpan {n : ℕ} (S : Submodule ℂ (MatrixPolynomial n))
    (hS : ∀ t p, p∈S → polynomialTorus n t p∈S) (p : MatrixPolynomial n)
    (hp : p∈S) : p∈polynomialWeightSpan S := by
  classical
  by_cases hp0 : p=0
  · rw [hp0]; exact Submodule.zero_mem _
  have hsupport : p.support.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hz
    apply hp0
    exact MvPolynomial.support_eq_empty.mp hz
  obtain ⟨d,hd⟩ := hsupport
  by_cases hh : ∀ e∈p.support, matrixMonomialWeight e=matrixMonomialWeight d
  · apply Submodule.subset_span
    refine ⟨hp,matrixMonomialWeight d,?_⟩
    intro t
    ext e
    rw [polynomialTorus_coeff_weight,MvPolynomial.coeff_smul,smul_eq_mul]
    by_cases he : e∈p.support
    · rw [hh e he]
    · have hz := MvPolynomial.notMem_support_iff.mp he
      rw [hz,mul_zero,mul_zero]
  · push Not at hh
    obtain ⟨e,he,hweight⟩ := hh
    obtain ⟨t,ht⟩ : ∃ t, integerWeightScalar (matrixMonomialWeight d) t≠
        integerWeightScalar (matrixMonomialWeight e) t := by
      by_contra hn
      push Not at hn
      exact hweight (integerWeightScalar_injective (funext hn)).symm
    let q := polynomialWeightFilter t (matrixMonomialWeight d) (matrixMonomialWeight e) p
    have hq : q∈S := S.smul_mem _ (S.sub_mem (hS t p hp) (S.smul_mem _ hp))
    have hr : p-q∈S := S.sub_mem hp hq
    have hq_lt : q.support.card<p.support.card :=
      (Finset.card_le_card (polynomialWeightFilter_support t _ p e)).trans_lt
        (Finset.card_erase_lt_of_mem he)
    have hr_lt : (p-q).support.card<p.support.card :=
      (Finset.card_le_card (polynomialWeightFilter_remainder_support t _ p d ht)).trans_lt
        (Finset.card_erase_lt_of_mem hd)
    have hqm := mem_polynomialWeightSpan S hS q hq
    have hrm := mem_polynomialWeightSpan S hS (p-q) hr
    have heq : p=q+(p-q) := by abel
    rw [heq]
    exact Submodule.add_mem _ hqm hrm
termination_by p.support.card

theorem polynomialWeightSpan_eq {n : ℕ} (S : Submodule ℂ (MatrixPolynomial n))
    (hS : ∀ t p, p∈S → polynomialTorus n t p∈S) : polynomialWeightSpan S=S := by
  apply le_antisymm
  · exact Submodule.span_le.mpr (fun p hp => hp.1)
  · exact fun p hp => mem_polynomialWeightSpan S hS p hp

end
end Schubert.RS.Representation
