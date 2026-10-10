import RSCounterexample.Paper.RootGeometricSeries
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Complete homogeneous polynomials of monomials in a coefficient window

For monomials `y_k = X^{d_k}` (`k ∈ K`) that all contain one fixed variable `X_t` exactly once, the
truncated sum `∑_{m ≤ B} h_m(y)` of complete homogeneous symmetric polynomials agrees with the
product of geometric series `∏_k (1 − y_k)^{−1}` in every coefficient `X^γ` with `γ ≤ β`, as soon as
`β_t ≤ B`: both count the exponent vectors `α` with `∑_k α_k d_k = γ`, and such an `α` has
`|α| = γ_t ≤ B`.

This is the step of Theorem 5.3 of the paper that identifies the product of the root factors
between two intervals with the characters of the graded pieces `Sym^ℓ(V_p ⊗ V_q^*)`.

## Main results

* `Schubert.RS.Quiver.coeff_hsymm`: the coefficient of `x^α` in `h_m` is `[|α| = m]`.
* `Schubert.RS.Quiver.coeff_aeval_monomial`: coefficients after substituting monomials for the
  variables.
* `Schubert.RS.Quiver.sum_hsymm_window`: the window comparison above.
-/

namespace Schubert.RS.Quiver

noncomputable section

open MvPolynomial

variable {K σ : Type*}

/-- The product of a multiset of variables is the monomial of its multiplicity function. -/
theorem prod_map_X_eq_monomial [DecidableEq K] (s : Multiset K) :
    (s.map (X : K → MvPolynomial K ℤ)).prod = monomial (Multiset.toFinsupp s) 1 := by
  rw [Finset.prod_multiset_map_count, ← prod_X_pow_eq_monomial, Multiset.toFinsupp_support]
  exact Finset.prod_congr rfl fun a _ => by rw [Multiset.toFinsupp_apply]

/-- The size of the multiplicity function of a multiset is its cardinality. -/
theorem sum_toFinsupp_apply [Fintype K] [DecidableEq K] (s : Multiset K) :
    ∑ k, Multiset.toFinsupp s k = Multiset.card s := by
  simp only [Multiset.toFinsupp_apply]
  exact Multiset.sum_count_eq_card fun a _ => Finset.mem_univ a

/-- **The coefficients of `h_m`**: every monomial of degree `m` has coefficient one. -/
theorem coeff_hsymm [Fintype K] [DecidableEq K] (m : ℕ) (α : K →₀ ℕ) :
    (hsymm K ℤ m).coeff α = if ∑ k, α k = m then 1 else 0 := by
  rw [hsymm, coeff_sum]
  simp only [prod_map_X_eq_monomial, coeff_monomial]
  by_cases hα : ∑ k, α k = m
  · have hcard : Multiset.card (Finsupp.toMultiset α) = m := by
      rw [← sum_toFinsupp_apply, Finsupp.toMultiset_toFinsupp, hα]
    rw [Finset.sum_eq_single ⟨Finsupp.toMultiset α, hcard⟩]
    · simp [Finsupp.toMultiset_toFinsupp, hα]
    · intro s _ hs
      have hne : Multiset.toFinsupp (s : Multiset K) ≠ α := by
        intro he
        apply hs
        apply Sym.ext
        change (s : Multiset K) = Finsupp.toMultiset α
        rw [← he, Multiset.toFinsupp_toMultiset]
      simp [hne]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · simp only [hα, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro s _
    have hne : Multiset.toFinsupp (s : Multiset K) ≠ α := by
      intro he
      apply hα
      rw [← he, sum_toFinsupp_apply]
      exact s.2
    simp [hne]

/-- Substituting the monomials `X^{d_k}` for the variables sends `x^α` to `X^{∑_k α_k d_k}`. -/
theorem aeval_monomial_monomial [Fintype K] (d : K → σ →₀ ℕ) (α : K →₀ ℕ) (z : ℤ) :
    aeval (fun k => (monomial (d k) 1 : MvPolynomial σ ℤ)) (monomial α z) =
      monomial (∑ k, α k • d k) z := by
  rw [aeval_monomial, monomial_sum_index, algebraMap_eq,
    Finsupp.prod_fintype _ _ (fun k => by simp)]
  simp only [monomial_pow, one_pow]

/-- **Coefficients after substituting monomials** for the variables: the coefficient of `X^γ` is
the sum of the coefficients of the `x^α` with `∑_k α_k d_k = γ`. -/
theorem coeff_aeval_monomial [Fintype K] [DecidableEq σ] (d : K → σ →₀ ℕ) (P : MvPolynomial K ℤ)
    (γ : σ →₀ ℕ) :
    (aeval (fun k => (monomial (d k) 1 : MvPolynomial σ ℤ)) P).coeff γ =
      ∑ α ∈ P.support with ∑ k, α k • d k = γ, P.coeff α := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum, coeff_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [aeval_monomial_monomial, coeff_monomial]

/-- The coefficients of `∑_{m ≤ B} h_m`: every monomial of degree at most `B` has coefficient
one. -/
theorem coeff_sum_hsymm [Fintype K] [DecidableEq K] (B : ℕ) (α : K →₀ ℕ) :
    (∑ m ∈ Finset.range (B + 1), hsymm K ℤ m).coeff α = if ∑ k, α k ≤ B then 1 else 0 := by
  rw [coeff_sum]
  simp only [coeff_hsymm]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

/-- The `t`-coordinate of `∑_k α_k d_k` is `|α|` when every `d_k` has `t`-coordinate one. -/
theorem sum_smul_apply_of_eq_one [Fintype K] (d : K → σ →₀ ℕ) {t : σ} (ht : ∀ k, d k t = 1)
    (α : K → ℕ) :
    (∑ k, α k • d k) t = ∑ k, α k := by
  simp [Finsupp.coe_finsetSum, Finset.sum_apply, ht]

/-- **The window comparison.** If every `d_k` has `t`-coordinate one and `β_t ≤ B`, then
`∑_{m ≤ B} h_m(X^{d_k} : k ∈ K)` and `∏_k (1 − X^{d_k})^{−1}` have the same coefficients at every
`γ ≤ β`. -/
theorem sum_hsymm_window [Fintype K] [DecidableEq K] [DecidableEq σ] (d : K → σ →₀ ℕ) (t : σ)
    (ht : ∀ k, d k t = 1)
    (β : σ →₀ ℕ) (B : ℕ) (hB : β t ≤ B) :
    WindowEq β
      ((∑ m ∈ Finset.range (B + 1),
          aeval (fun k => (monomial (d k) 1 : MvPolynomial σ ℤ)) (hsymm K ℤ m) :
        MvPolynomial σ ℤ) : MvPowerSeries σ ℤ)
      (∏ k, rootGeometricSeries (d k)) := by
  classical
  refine WindowEq.trans ?_ (boundedRootProduct_window_geometric d (fun _ => t) ht β)
  intro γ hγ
  let inst : Fintype (DegreeFiber d γ) := (degree_fiber_finite d (fun _ => t) ht γ).fintype
  rw [MvPolynomial.coeff_coe, MvPolynomial.coeff_coe,
    boundedRootProduct_coefficient d (fun _ => t) ht β γ hγ, ← map_sum, coeff_aeval_monomial]
  set P : MvPolynomial K ℤ := ∑ m ∈ Finset.range (B + 1), hsymm K ℤ m with hPdef
  have hP (α : K →₀ ℕ) : P.coeff α = if ∑ k, α k ≤ B then 1 else 0 := coeff_sum_hsymm B α
  have hsize (α : K →₀ ℕ) (hα : ∑ k, α k • d k = γ) : ∑ k, α k ≤ B := by
    have h1 := sum_smul_apply_of_eq_one d ht α
    rw [hα] at h1
    rw [← h1]
    exact (hγ t).trans hB
  have hone : ∀ α ∈ P.support.filter (fun α => ∑ k, α k • d k = γ), P.coeff α = 1 := by
    intro α hα
    simp only [hP, hsize α (Finset.mem_filter.mp hα).2, ↓reduceIte]
  rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  symm
  rw [← Finset.card_map Finsupp.equivFunOnFinite.toEmbedding]
  refine @Fintype.card_of_subtype _ (fun x : K → ℕ => ∑ r, x r • d r = γ) _ ?_ inst
  intro a
  simp only [Finset.mem_map_equiv, Finset.mem_filter]
  constructor
  · intro h
    have h2 := h.2
    simpa [Finsupp.equivFunOnFinite] using h2
  · intro ha
    have hα : ∑ k, (Finsupp.equivFunOnFinite.symm a) k • d k = γ := by simpa using ha
    refine ⟨?_, hα⟩
    have hs := hsize _ hα
    rw [MvPolynomial.mem_support_iff, hP]
    simp only [Finsupp.coe_equivFunOnFinite_symm] at hs
    simp [hs]

end

end Schubert.RS.Quiver
