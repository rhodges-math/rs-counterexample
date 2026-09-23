import Schubert.RS.JosephPolo.OrbitDuality

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators ComplexConjugate

variable {σ ι : Type*} [Fintype ι]

def polynomialGram (p : ι → MvPolynomial σ ℂ) :
    Module.Dual ℂ (MvPolynomial σ ℂ) →ₗ[ℂ] MvPolynomial σ ℂ where
  toFun f := ∑ i, f (p i) • p i
  map_add' f g := by simp only [LinearMap.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [LinearMap.smul_apply,Finset.smul_sum,smul_smul,RingHom.id_apply,smul_eq_mul]

theorem polynomialGram_range (p : ι → MvPolynomial σ ℂ)
    (hp : ∀ i m, conj (MvPolynomial.coeff m (p i)) = MvPolynomial.coeff m (p i)) :
    LinearMap.range (polynomialGram p) = Submodule.span ℂ (Set.range p) := by
  classical
  apply le_antisymm
  · rintro q ⟨f,rfl⟩
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)
  · have hg := real_polynomial_gram_span p hp (LinearMap.id : MvPolynomial σ ℂ →ₗ[ℂ] _)
    simp only [LinearMap.id_apply] at hg
    rw [← hg]
    apply Submodule.span_le.mpr
    rintro q ⟨m,rfl⟩
    exact ⟨MvPolynomial.lcoeff ℂ m,rfl⟩

theorem polynomialGram_orbit {Ω : Type*} (p : ι → MvPolynomial σ ℂ)
    (φ : MvPolynomial σ ℂ →ₗ[ℂ] (Ω → ℂ)) (ρ : Ω → MvPolynomial σ ℂ)
    (hρ : ∀ w, ρ w = ∑ i, φ (p i) w • p i)
    (f : Module.Dual ℂ (MvPolynomial σ ℂ)) :
    φ (polynomialGram p f) = orbitFunctionals ρ f := by
  funext w
  simp [polynomialGram,orbitFunctionals,hρ,map_sum,map_smul,smul_eq_mul,mul_comm]

/-- The same Gram witness works for both restrictions. Hence inclusion of
actual orbit spans transfers vanishing of every polynomial in the minor span. -/
theorem restriction_zero_of_orbitSpan_le {Ω Λ : Type*} (p : ι → MvPolynomial σ ℂ)
    (hp : ∀ i m, conj (MvPolynomial.coeff m (p i)) = MvPolynomial.coeff m (p i))
    (φ : MvPolynomial σ ℂ →ₗ[ℂ] (Ω → ℂ)) (ρ : Ω → MvPolynomial σ ℂ)
    (hρ : ∀ w, ρ w = ∑ i, φ (p i) w • p i)
    (ψ : MvPolynomial σ ℂ →ₗ[ℂ] (Λ → ℂ)) (τ : Λ → MvPolynomial σ ℂ)
    (hτ : ∀ w, τ w = ∑ i, ψ (p i) w • p i)
    (hle : Submodule.span ℂ (Set.range τ) ≤ Submodule.span ℂ (Set.range ρ))
    (q : MvPolynomial σ ℂ) (hq : q ∈ Submodule.span ℂ (Set.range p))
    (hz : φ q = 0) : ψ q = 0 := by
  obtain ⟨f,hf⟩ : q ∈ LinearMap.range (polynomialGram p) := by
    rwa [polynomialGram_range p hp]
  have hφ : orbitFunctionals ρ f = 0 :=
    (polynomialGram_orbit p φ ρ hρ f).symm.trans ((congrArg φ hf).trans hz)
  have hker : Submodule.span ℂ (Set.range ρ) ≤ LinearMap.ker f := by
    apply Submodule.span_le.mpr
    rintro x ⟨w,rfl⟩
    exact congrFun hφ w
  rw [← hf,polynomialGram_orbit p ψ τ hτ]
  funext w
  exact hker (hle (Submodule.subset_span ⟨w,rfl⟩))

end
end Schubert.RS.Representation
