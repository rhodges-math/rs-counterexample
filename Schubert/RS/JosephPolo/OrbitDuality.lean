import Schubert.RS.JosephPolo.PolynomialGramSpan

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators ComplexConjugate

variable {Ω V : Type*} [AddCommGroup V] [Module ℂ V]

def orbitFunctionals (ρ : Ω → V) : Module.Dual ℂ V →ₗ[ℂ] (Ω → ℂ) where
  toFun f w := f (ρ w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def orbitSpanFunctionals (ρ : Ω → V) :
    Module.Dual ℂ (Submodule.span ℂ (Set.range ρ)) →ₗ[ℂ] (Ω → ℂ) where
  toFun f w := f ⟨ρ w,Submodule.subset_span ⟨w,rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem orbitSpanFunctionals_injective (ρ : Ω → V) :
    Function.Injective (orbitSpanFunctionals ρ) := by
  intro f g h
  apply LinearMap.ext
  rintro ⟨x,hx⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w,rfl⟩ := hx
    exact congrFun h w
  | zero => exact (map_zero f).trans (map_zero g).symm
  | add x y hx hy ihx ihy =>
    change f (⟨x,hx⟩ + ⟨y,hy⟩) = g (⟨x,hx⟩ + ⟨y,hy⟩)
    rw [map_add,map_add,ihx,ihy]
  | smul c x hx ih =>
    change f (c • (⟨x,hx⟩ : Submodule.span ℂ (Set.range ρ))) = g (c • ⟨x,hx⟩)
    rw [map_smul,map_smul,ih]

theorem orbitSpanFunctionals_range (ρ : Ω → V) :
    LinearMap.range (orbitSpanFunctionals ρ) = LinearMap.range (orbitFunctionals ρ) := by
  ext h
  constructor
  · rintro ⟨f,rfl⟩
    obtain ⟨g,hg⟩ := LinearMap.dualMap_surjective_of_injective
      (Submodule.span ℂ (Set.range ρ)).injective_subtype f
    refine ⟨g,?_⟩
    rw [← hg]
    rfl
  · rintro ⟨f,rfl⟩
    exact ⟨f.comp (Submodule.span ℂ (Set.range ρ)).subtype,rfl⟩

/-- The mixed expansion identifies the orbit's coefficient functions with
the span of restricted minor products, including all polynomial relations. -/
theorem polynomialOrbitFunctionals_range {σ ι : Type*} [Fintype ι]
    (p : ι → MvPolynomial σ ℂ)
    (hp : ∀ i m, conj (MvPolynomial.coeff m (p i)) = MvPolynomial.coeff m (p i))
    (φ : MvPolynomial σ ℂ →ₗ[ℂ] (Ω → ℂ)) (ρ : Ω → MvPolynomial σ ℂ)
    (hρ : ∀ w, ρ w = ∑ i, φ (p i) w • p i) :
    LinearMap.range (orbitFunctionals ρ) = Submodule.span ℂ (Set.range (fun i => φ (p i))) := by
  classical
  apply le_antisymm
  · rintro x ⟨f,rfl⟩
    have he : orbitFunctionals ρ f = ∑ i, f (p i) • φ (p i) := by
      funext w
      simp [orbitFunctionals,hρ,map_sum,map_smul,smul_eq_mul,mul_comm]
    rw [he]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)
  · rw [← real_polynomial_gram_span p hp φ]
    apply Submodule.span_le.mpr
    rintro x ⟨m,rfl⟩
    refine ⟨MvPolynomial.lcoeff ℂ m,?_⟩
    funext w
    simp [orbitFunctionals,hρ,MvPolynomial.coeff_sum,MvPolynomial.coeff_smul,smul_eq_mul,mul_comm]

/-- A nondegenerate pairing between the actual orbit span and its restricted
coordinate model. This is independent of a character formula or a basis. -/
def polynomialOrbitDuality {σ ι : Type*} [Fintype ι]
    (p : ι → MvPolynomial σ ℂ)
    (hp : ∀ i m, conj (MvPolynomial.coeff m (p i)) = MvPolynomial.coeff m (p i))
    (φ : MvPolynomial σ ℂ →ₗ[ℂ] (Ω → ℂ)) (ρ : Ω → MvPolynomial σ ℂ)
    (hρ : ∀ w, ρ w = ∑ i, φ (p i) w • p i) :
    Module.Dual ℂ (Submodule.span ℂ (Set.range ρ)) ≃ₗ[ℂ]
      Submodule.span ℂ (Set.range (fun i => φ (p i))) :=
  (LinearEquiv.ofInjective (orbitSpanFunctionals ρ) (orbitSpanFunctionals_injective ρ)).trans
    (LinearEquiv.ofEq _ _ ((orbitSpanFunctionals_range ρ).trans
      (polynomialOrbitFunctionals_range p hp φ ρ hρ)))

end
end Schubert.RS.Representation
