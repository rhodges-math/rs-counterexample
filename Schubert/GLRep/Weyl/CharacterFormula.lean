import Schubert.GLRep.Weyl.Eigen
import TauCeti.RepresentationTheory.ClassicalGroups.DominantWeight

/-!
# The Weyl character formula from the Laplacian eigen-equation

Let `χ` be a symmetric Laurent polynomial over a field of characteristic zero whose exponents are
all dominated by a weakly decreasing `λ`, with coefficient `1` at `λ`. If `a_δ χ` is an
eigenvector of the Laplacian with eigenvalue `|λ + δ|²`, then `a_δ χ = a_{λ+δ}`
(`GLRep.LaurentPoly.alternant_staircase_mul_eq`).

The proof is the classical one. `a_δ χ` is antisymmetric. Its exponents are dominated by `λ + δ`
and have norm `|λ + δ|`; the strictly decreasing ones are therefore equal to `λ + δ`, by strict
convexity. An antisymmetric Laurent polynomial supported on the rearrangements of `λ + δ` is a
multiple of `a_{λ+δ}`, and the multiple is the coefficient of `x^λ` in `χ`.

Combined with Jacobi's bialternant formula, this identifies `χ` with the Schur polynomial `s_λ`
when `χ` is a polynomial (`GLRep.LaurentPoly.eq_diagramSchurPoly_of_alternant_mul_eq`).

## Main results

* `GLRep.LaurentPoly.coeff_alternant_mul`: the coefficients of `a_α f`.
* `GLRep.LaurentPoly.alternant_staircase_mul_eq`: the Weyl character formula, abstractly.
-/

namespace GLRep

open Finset Equiv

noncomputable section

namespace LaurentPoly

variable {K : Type*} [Field K] {n : ℕ}

theorem coeff_single_mul (a : Fin n → ℤ) (c : K) (g : LaurentPoly K n) (ν : Fin n → ℤ) :
    (AddMonoidAlgebra.single a c * g).coeff ν = c * g.coeff (ν - a) := by
  have h := AddMonoidAlgebra.coeff_single_mul_add g c a (ν - a)
  rwa [add_sub_cancel] at h

/-- The coefficients of `a_α f`. -/
theorem coeff_alternant_mul (α : Fin n → ℤ) (f : LaurentPoly K n) (ν : Fin n → ℤ) :
    (alternant α * f).coeff ν =
      ∑ σ : Perm (Fin n), ((Perm.sign σ : ℤ) : K) * f.coeff (ν - α ∘ σ.symm) := by
  rw [alternant, sum_mul, AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  exact sum_congr rfl fun σ _ => coeff_single_mul _ _ _ _

theorem coeff_laplace (f : LaurentPoly K n) (ν : Fin n → ℤ) :
    (laplace f).coeff ν = (normSq ν : K) * f.coeff ν := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hf, hg,
      mul_add]
  | single μ c =>
    rw [laplace_single, AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply, Finsupp.single_apply]
    split_ifs with h
    · rw [h]
    · rw [mul_zero]

/-- Partial sums determine a weight. -/
theorem eq_of_partialSum_eq {μ ν : Fin n → ℤ} (h : ∀ k, partialSum μ k = partialSum ν k) :
    μ = ν := by
  funext i
  have h1 := h (i + 1)
  rw [partialSum_succ, partialSum_succ, h i] at h1
  exact add_left_cancel h1

/-- The dominance order is antisymmetric. -/
theorem Dominated.antisymm {μ ν : Fin n → ℤ} (h₁ : Dominated μ ν) (h₂ : Dominated ν μ) :
    μ = ν :=
  eq_of_partialSum_eq fun k => le_antisymm (h₁.1 k) (h₂.1 k)

variable [CharZero K]

/-- An antisymmetric Laurent polynomial vanishes at exponents with a repeated entry. -/
theorem IsAntisymm.coeff_eq_zero_of_not_injective {F : LaurentPoly K n} (hF : IsAntisymm F)
    {ν : Fin n → ℤ} (hν : ¬Function.Injective ν) : F.coeff ν = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hν
  have hfix : ν ∘ Equiv.swap i j = ν := by
    funext k
    simp only [Function.comp_apply]
    rcases eq_or_ne k i with rfl | hki
    · simp [hij]
    rcases eq_or_ne k j with rfl | hkj
    · simp [hij]
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have h := hF.coeff_comp (Equiv.swap i j) ν
  rw [hfix, Perm.sign_swap hne] at h
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul] at h
  have h2 : (2 : K) * F.coeff ν = 0 := by linear_combination h
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

/-- Every injective exponent vector has a strictly decreasing rearrangement. -/
theorem exists_strictAnti_comp {ν : Fin n → ℤ} (hν : Function.Injective ν) :
    ∃ τ : Perm (Fin n), StrictAnti (ν ∘ τ) := by
  refine ⟨Tuple.sort (fun i => -ν i), ?_⟩
  have hm := Tuple.monotone_sort (fun i => -ν i)
  have ha : Antitone (ν ∘ Tuple.sort (fun i => -ν i)) := fun i j hij => by
    have := hm hij
    simp only [Function.comp_apply] at this ⊢
    linarith
  exact ha.strictAnti_of_injective (hν.comp (Equiv.injective _))

/-- **The Weyl character formula, abstractly.** -/
theorem alternant_staircase_mul_eq (χ : LaurentPoly K n) (hsymm : IsSymm χ) (lam : Fin n → ℤ)
    (hlam : Antitone lam) (hsupp : ∀ μ, χ.coeff μ ≠ 0 → Dominated μ lam)
    (hlam1 : χ.coeff lam = 1)
    (heig : laplace (alternant (staircase n) * χ) =
      (normSq (lam + staircase n) : K) • (alternant (staircase n) * χ)) :
    alternant (staircase n) * χ = alternant (lam + staircase n) := by
  set δ := staircase n
  set Λ := lam + δ
  set F := alternant δ * χ with hF_def
  have hδ : StrictAnti δ := staircase_strictAnti n
  have hΛ : StrictAnti Λ := hlam.add_strictAnti hδ
  have hanti : IsAntisymm F := (isAntisymm_alternant δ).mul_isSymm hsymm
  -- the exponents of `F` are dominated by `Λ`
  have hdom : ∀ ν, F.coeff ν ≠ 0 → Dominated ν Λ := by
    intro ν hν
    rw [hF_def, coeff_alternant_mul] at hν
    obtain ⟨σ, -, hσ⟩ := exists_ne_zero_of_sum_ne_zero hν
    have hχ : χ.coeff (ν - δ ∘ σ.symm) ≠ 0 := right_ne_zero_of_mul hσ
    have := dominated_add (hsupp _ hχ) (dominated_comp_perm hδ.antitone σ.symm)
    rwa [sub_add_cancel] at this
  -- the exponents of `F` have norm `|Λ|`
  have hnorm : ∀ ν, F.coeff ν ≠ 0 → normSq ν = normSq Λ := by
    intro ν hν
    have h := congrArg (fun G : LaurentPoly K n => G.coeff ν) heig
    simp only [coeff_laplace, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul] at h
    exact Int.cast_injective (mul_right_cancel₀ hν h)
  -- so they are the rearrangements of `Λ`
  have hsupp' : ∀ ν, F.coeff ν ≠ 0 → ∃ σ : Perm (Fin n), ν = Λ ∘ σ := by
    intro ν hν
    have hinj : Function.Injective ν := by
      by_contra h
      exact hν (hanti.coeff_eq_zero_of_not_injective h)
    obtain ⟨τ, hτ⟩ := exists_strictAnti_comp hinj
    have hτν : F.coeff (ν ∘ τ) ≠ 0 := by
      rw [hanti.coeff_comp]
      exact mul_ne_zero (by rcases Int.units_eq_one_or (Perm.sign τ) with h | h <;> simp [h]) hν
    have heq := eq_of_dominated_of_normSq_eq hΛ hτ.antitone (hdom _ hτν)
      ((hnorm _ hτν).trans rfl)
    refine ⟨τ.symm, ?_⟩
    rw [← heq]
    funext i
    simp
  rw [eq_smul_alternant hanti hΛ.injective hsupp']
  -- the coefficient of `x^Λ`
  have hcoeff : F.coeff Λ = 1 := by
    rw [hF_def, coeff_alternant_mul, sum_eq_single 1]
    · have h1 : Λ - δ ∘ ⇑(Equiv.symm (1 : Perm (Fin n))) = lam := by
        funext i
        change lam i + δ i - δ i = lam i
        ring
      rw [h1, hlam1, Perm.sign_one]
      simp
    · intro σ _ hσ
      have hz : χ.coeff (Λ - δ ∘ σ.symm) = 0 := by
        by_contra hne
        apply hσ
        have h1 := hsupp _ hne
        have h2 : Dominated δ (δ ∘ σ.symm) := by
          refine ⟨fun k => ?_, (Equiv.sum_comp σ.symm δ).symm⟩
          have := h1.1 k
          simp only [Λ] at this
          rw [show lam + δ - δ ∘ ⇑σ.symm = lam + (δ - δ ∘ ⇑σ.symm) by abel, partialSum_add,
            show δ - δ ∘ ⇑σ.symm = δ + -(δ ∘ ⇑σ.symm) by abel, partialSum_add] at this
          simp only [partialSum, Pi.neg_apply, sum_neg_distrib] at this ⊢
          linarith
        have h3 := Dominated.antisymm h2 (dominated_comp_perm hδ.antitone σ.symm)
        have : σ.symm = 1 := by
          ext i
          exact congrArg Fin.val (hδ.injective (congrFun h3 i)).symm
        rw [← Perm.inv_def] at this
        exact inv_eq_one.mp this
      rw [hz, mul_zero]
    · simp
  rw [hcoeff, one_smul]

end LaurentPoly

end

end GLRep
