import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.LinearAlgebra.Finsupp.LSum
import TauCeti.RingTheory.MvPolynomial.Symmetric.Alternant

/-!
# Laurent polynomials, Euler operators and alternants

The Laurent polynomials in `n` variables with coefficients in a commutative ring `R` are the
monoid algebra `R[ℤⁿ]` (`GLRep.LaurentPoly R n`); the monomial `x^μ` is
`AddMonoidAlgebra.single μ 1`. This file provides the tools used in the proof of the Weyl
character formula:

* the **Euler operators** `θ_k : x^μ ↦ μ_k x^μ` (`GLRep.LaurentPoly.euler`), which are derivations,
  and the **Laplacian** `D = ∑_k θ_k²` (`GLRep.LaurentPoly.laplace`), which multiplies `x^μ` by
  `|μ|² = ∑_k μ_k²` and satisfies `D(fg) = D(f) g + 2 ∑_k θ_k(f) θ_k(g) + f D(g)`;
* the permutation action, **antisymmetric** Laurent polynomials and the **alternants**
  `a_α = ∑_σ sign(σ) x^{α ∘ σ⁻¹}`;
* the embedding of polynomials (`GLRep.LaurentPoly.ofPoly`), which sends Tau Ceti's alternants to
  alternants.

## Main definitions

* `GLRep.LaurentPoly R n`, `GLRep.LaurentPoly.euler`, `GLRep.LaurentPoly.laplace`,
  `GLRep.LaurentPoly.permute`, `GLRep.LaurentPoly.IsAntisymm`, `GLRep.LaurentPoly.alternant`,
  `GLRep.LaurentPoly.ofPoly`.

## Main results

* `GLRep.LaurentPoly.euler_mul`, `GLRep.LaurentPoly.laplace_mul`: the product rules.
* `GLRep.LaurentPoly.laplace_alternant`: `D a_α = |α|² a_α`.
* `GLRep.LaurentPoly.isAntisymm_alternant`, `GLRep.LaurentPoly.IsAntisymm.mul_isSymm`: `a_α f` is
  antisymmetric for symmetric `f`.
* `GLRep.LaurentPoly.eq_smul_alternant`: an antisymmetric Laurent polynomial all of whose
  exponents are rearrangements of one strictly decreasing `Λ` is a multiple of `a_Λ`.
* `GLRep.LaurentPoly.ofPoly_alternant`.
-/

namespace GLRep

open Equiv

noncomputable section

/-- The Laurent polynomials in `n` variables over `R`, the monoid algebra `R[ℤⁿ]`. -/
abbrev LaurentPoly (R : Type*) [CommRing R] (n : ℕ) := AddMonoidAlgebra R (Fin n → ℤ)

namespace LaurentPoly

variable {R : Type*} [CommRing R] {n : ℕ}

/-! ### Euler operators and the Laplacian -/

/-- The **Euler operator** `θ_k : x^μ ↦ μ_k x^μ`. -/
def euler (k : Fin n) : LaurentPoly R n →ₗ[R] LaurentPoly R n :=
  (AddMonoidAlgebra.coeffLinearEquiv R).symm.toLinearMap ∘ₗ
    Finsupp.lsum R (fun μ : Fin n → ℤ => Finsupp.lsingle μ ∘ₗ ((μ k : R) • LinearMap.id)) ∘ₗ
    (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

@[simp] theorem euler_single (k : Fin n) (μ : Fin n → ℤ) (c : R) :
    euler k (AddMonoidAlgebra.single μ c) = AddMonoidAlgebra.single μ ((μ k : R) * c) := by
  change (AddMonoidAlgebra.coeffLinearEquiv R).symm
    (Finsupp.lsum R _ (AddMonoidAlgebra.single μ c).coeff) = _
  rw [AddMonoidAlgebra.coeff_single, Finsupp.lsum_single]
  rfl

/-- **The Euler operators are derivations.** -/
theorem euler_mul (k : Fin n) (f g : LaurentPoly R n) :
    euler k (f * g) = euler k f * g + f * euler k g := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => rw [add_mul, map_add, h₁, h₂, map_add, add_mul, add_mul]; abel
  | single μ a =>
    induction g using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add g₁ g₂ h₁ h₂ => rw [mul_add, map_add, h₁, h₂, map_add, mul_add, mul_add]; abel
    | single ν b =>
      simp only [AddMonoidAlgebra.single_mul_single, euler_single, Pi.add_apply, Int.cast_add]
      rw [← AddMonoidAlgebra.single_add]
      congr 1
      ring

/-- The **Laplacian** `D = ∑_k θ_k²`, which multiplies `x^μ` by `|μ|²`. -/
def laplace : LaurentPoly R n →ₗ[R] LaurentPoly R n := ∑ k, euler k ∘ₗ euler k

/-- The squared norm `|μ|² = ∑_k μ_k²`. -/
def normSq (μ : Fin n → ℤ) : ℤ := ∑ k, μ k * μ k

@[simp] theorem laplace_single (μ : Fin n → ℤ) (c : R) :
    laplace (AddMonoidAlgebra.single μ c) = AddMonoidAlgebra.single μ ((normSq μ : R) * c) := by
  have h1 : ∀ r : R, AddMonoidAlgebra.single μ r = AddMonoidAlgebra.singleAddHom μ r :=
    fun _ => rfl
  simp only [laplace, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
    normSq, Int.cast_sum, Int.cast_mul, Finset.sum_mul, h1, map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [← h1, euler_single, euler_single, mul_assoc, h1]

/-- **The product rule for the Laplacian**: `D(fg) = D(f) g + 2 ∑_k θ_k(f) θ_k(g) + f D(g)`. -/
theorem laplace_mul (f g : LaurentPoly R n) :
    laplace (f * g) = laplace f * g + 2 * ∑ k, euler k f * euler k g + f * laplace g := by
  simp only [laplace, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, euler_mul,
    map_add, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-! ### The permutation action and alternants -/

/-- The substitution `x_i ↦ x_{σ i}`: the exponent `μ` goes to `μ ∘ σ⁻¹`. -/
def permute (σ : Perm (Fin n)) : LaurentPoly R n ≃+* LaurentPoly R n :=
  AddMonoidAlgebra.mapDomainRingEquiv R
    { toFun := fun μ => μ ∘ σ.symm
      invFun := fun μ => μ ∘ σ
      left_inv := fun μ => by ext; simp
      right_inv := fun μ => by ext; simp
      map_add' := fun _ _ => rfl }

@[simp] theorem permute_single (σ : Perm (Fin n)) (μ : Fin n → ℤ) (c : R) :
    permute σ (AddMonoidAlgebra.single μ c) = AddMonoidAlgebra.single (μ ∘ σ.symm) c :=
  AddMonoidAlgebra.mapDomainRingEquiv_single _ _ _

theorem coeff_permute (σ : Perm (Fin n)) (f : LaurentPoly R n) (μ : Fin n → ℤ) :
    (permute σ f).coeff μ = f.coeff (μ ∘ σ) := by
  simp only [permute, AddMonoidAlgebra.coeff_mapDomainRingEquiv, Finsupp.equivMapDomain_apply]
  rfl

/-- `f` is **symmetric**: invariant under all permutations of the variables. -/
def IsSymm (f : LaurentPoly R n) : Prop := ∀ σ : Perm (Fin n), permute σ f = f

/-- `f` is **antisymmetric**: `permute σ f = sign(σ) f` for every permutation `σ`. -/
def IsAntisymm (f : LaurentPoly R n) : Prop :=
  ∀ σ : Perm (Fin n), permute σ f = ((Perm.sign σ : ℤ) : R) • f

theorem IsAntisymm.coeff_comp {f : LaurentPoly R n} (hf : IsAntisymm f) (σ : Perm (Fin n))
    (μ : Fin n → ℤ) : f.coeff (μ ∘ σ) = ((Perm.sign σ : ℤ) : R) * f.coeff μ := by
  rw [← coeff_permute, hf σ, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]

theorem IsAntisymm.mul_isSymm {f g : LaurentPoly R n} (hf : IsAntisymm f) (hg : IsSymm g) :
    IsAntisymm (f * g) := fun σ => by
  rw [map_mul, hf σ, hg σ, smul_mul_assoc]

/-- The **alternant** `a_α = ∑_σ sign(σ) x^{α ∘ σ⁻¹}`. -/
def alternant (α : Fin n → ℤ) : LaurentPoly R n :=
  ∑ σ : Perm (Fin n), AddMonoidAlgebra.single (α ∘ σ.symm) ((Perm.sign σ : ℤ) : R)

theorem normSq_comp (μ : Fin n → ℤ) (σ : Perm (Fin n)) : normSq (μ ∘ σ) = normSq μ := by
  simp only [normSq, Function.comp_apply]
  exact Equiv.sum_comp σ (fun k => μ k * μ k)

/-- `D a_α = |α|² a_α`. -/
theorem laplace_alternant (α : Fin n → ℤ) :
    laplace (alternant α : LaurentPoly R n) = (normSq α : R) • alternant α := by
  simp only [alternant, map_sum, laplace_single, Finset.smul_sum, AddMonoidAlgebra.smul_single,
    smul_eq_mul, normSq_comp]

theorem coeff_alternant (α μ : Fin n → ℤ) :
    (alternant α : LaurentPoly R n).coeff μ =
      ∑ σ : Perm (Fin n), if α ∘ σ.symm = μ then ((Perm.sign σ : ℤ) : R) else 0 := by
  simp only [alternant, AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum, Finset.sum_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem permute_alternant (σ : Perm (Fin n)) (α : Fin n → ℤ) :
    permute σ (alternant α : LaurentPoly R n) = ((Perm.sign σ : ℤ) : R) • alternant α := by
  simp only [alternant, map_sum, permute_single, Finset.smul_sum, AddMonoidAlgebra.smul_single,
    smul_eq_mul]
  refine Fintype.sum_equiv (Equiv.mulLeft σ) _ _ fun τ => ?_
  have hexp : α ∘ ⇑τ.symm ∘ ⇑σ.symm = α ∘ ⇑(σ * τ).symm := by
    ext i
    simp [Perm.mul_def]
  have hcoef : ((Perm.sign τ : ℤ) : R) =
      ((Perm.sign σ : ℤ) : R) * ((Perm.sign (σ * τ) : ℤ) : R) := by
    have h := Int.units_mul_self (Perm.sign σ)
    calc ((Perm.sign τ : ℤ) : R) = ((Perm.sign σ * Perm.sign σ * Perm.sign τ : ℤˣ) : ℤ) := by
          rw [h, one_mul]
      _ = _ := by rw [Perm.sign_mul]; push_cast; ring
  rw [Equiv.coe_mulLeft, ← hexp, ← hcoef]
  rfl

theorem isAntisymm_alternant (α : Fin n → ℤ) : IsAntisymm (alternant α : LaurentPoly R n) :=
  fun σ => permute_alternant σ α

/-- **An antisymmetric Laurent polynomial supported on the rearrangements of one injective `Λ`
is a multiple of `a_Λ`.** -/
theorem eq_smul_alternant {F : LaurentPoly R n} (hF : IsAntisymm F) {Λ : Fin n → ℤ}
    (hΛ : Function.Injective Λ) (hsupp : ∀ ν, F.coeff ν ≠ 0 → ∃ σ : Perm (Fin n), ν = Λ ∘ σ) :
    F = F.coeff Λ • alternant Λ := by
  ext ν
  rw [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, coeff_alternant]
  by_cases hν : ∃ σ : Perm (Fin n), ν = Λ ∘ σ
  · obtain ⟨σ, rfl⟩ := hν
    rw [hF.coeff_comp σ Λ, Finset.sum_eq_single σ⁻¹]
    · simp only [show Λ ∘ ⇑(σ⁻¹).symm = Λ ∘ ⇑σ from rfl, ↓reduceIte, Perm.sign_inv]
      ring
    · intro τ _ hτ
      have hne : ¬(Λ ∘ ⇑τ.symm = Λ ∘ ⇑σ) := by
        intro h
        apply hτ
        have : τ.symm = σ := by
          ext i
          exact congrArg _ (hΛ (congrFun h i))
        rw [← this]
        rfl
      simp only [hne, ↓reduceIte]
    · simp
  · have h0 : F.coeff ν = 0 := by
      by_contra h
      exact hν (hsupp ν h)
    rw [h0]
    symm
    rw [Finset.sum_eq_zero, mul_zero]
    intro τ _
    have hne : ¬(Λ ∘ ⇑τ.symm = ν) := fun h => hν ⟨τ.symm, h.symm⟩
    simp only [hne, ↓reduceIte]

/-! ### Polynomials as Laurent polynomials -/

/-- Exponent vectors of monomials as integer weights. -/
def expToWeight : (Fin n →₀ ℕ) →+ (Fin n → ℤ) where
  toFun a i := a i
  map_zero' := by funext i; simp
  map_add' a b := by funext i; simp

theorem expToWeight_injective : Function.Injective (expToWeight (n := n)) := fun a b h =>
  Finsupp.ext fun i => by simpa [expToWeight] using congrFun h i

variable (R n) in
/-- The embedding of polynomials into Laurent polynomials. -/
def ofPoly : MvPolynomial (Fin n) R →+* LaurentPoly R n :=
  AddMonoidAlgebra.mapDomainRingHom R expToWeight

theorem ofPoly_injective : Function.Injective (ofPoly R n) :=
  AddMonoidAlgebra.mapDomain_injective expToWeight_injective

@[simp] theorem ofPoly_monomial (a : Fin n →₀ ℕ) (c : R) :
    ofPoly R n (MvPolynomial.monomial a c) = AddMonoidAlgebra.single (expToWeight a) c :=
  AddMonoidAlgebra.mapDomain_single

theorem ofPoly_X (i : Fin n) :
    ofPoly R n (MvPolynomial.X i) = AddMonoidAlgebra.single (Pi.single i 1) 1 := by
  rw [MvPolynomial.X, ofPoly_monomial]
  congr 1
  funext j
  simp [expToWeight, Pi.single_apply, Finsupp.single_apply, eq_comm]

/-- **Tau Ceti's alternants are alternants**: `a_α = det(X_i^{α_j})` becomes
`∑_σ sign(σ) x^{α ∘ σ⁻¹}`. -/
theorem ofPoly_alternant (α : Fin n → ℕ) :
    ofPoly R n (TauCeti.alternant (Fin n) R α) = alternant fun i => (α i : ℤ) := by
  rw [TauCeti.alternant_eq_sum, map_sum, alternant]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Units.smul_def, map_zsmul, map_prod]
  simp only [map_pow, ofPoly_X, AddMonoidAlgebra.single_pow, one_pow]
  rw [AddMonoidAlgebra.prod_single, Finset.prod_const_one, zsmul_eq_mul,
    AddMonoidAlgebra.intCast_def, AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
  congr 1
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, Function.comp_apply]
  rw [Finset.sum_eq_single (τ.symm j)]
  · simp
  · intro i _ hi
    have hne : ¬(j = τ i) := by
      rintro rfl
      exact hi (by simp)
    simp only [hne, ↓reduceIte, smul_zero]
  · simp

end LaurentPoly

end

end GLRep
