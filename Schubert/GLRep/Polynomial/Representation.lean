import Schubert.GLRep.Polynomial.Functions
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import TauCeti.RepresentationTheory.MatrixCoefficients

/-!
# Representations with matrix coefficients in a given algebra of functions

Let `A` be a subalgebra of the functions `G → K` on a monoid `G`. A representation `ρ` of `G` on
`W` has *coefficients in `A`* (`GLRep.HasCoeffsIn A ρ`) when `W` is finite-dimensional and every
matrix coefficient `g ↦ f (ρ g w)`, for `f` a linear form and `w` a vector, lies in `A`.

For `A` the polynomial functions in the matrix entries, this is the notion of a **polynomial
representation** of `GL_n(K)` (`GLRep.IsPolynomialRep`) and of a Levi group
`∏_p GL_{d_p}(K)` (`GLRep.IsPolynomialLeviRep`).

The definition does not mention a basis. Against any basis, it is equivalent to all entries of
the matrices `ρ g` lying in `A` (`GLRep.hasCoeffsIn_iff_toMatrix`).

## Main results

* `GLRep.HasCoeffsIn.of_injective`, `GLRep.HasCoeffsIn.of_surjective`: subrepresentations and
  quotients, and more generally sources of injective and targets of surjective intertwining maps.
* `GLRep.HasCoeffsIn.prod`, `GLRep.HasCoeffsIn.tprod`, `GLRep.HasCoeffsIn.piTensor`: products,
  tensor products, and tensor products of finite families.
* `GLRep.HasCoeffsIn.comp`: restriction along a monoid homomorphism.
* `GLRep.HasCoeffsIn.trivial`: trivial representations.
-/

namespace GLRep

open Module

noncomputable section

variable {K : Type*} [Field K] {G : Type*} [Monoid G]

/-- The representation `ρ` is finite-dimensional and all its matrix coefficients
`g ↦ f (ρ g w)` lie in the algebra of functions `A`. -/
structure HasCoeffsIn (A : Subalgebra K (G → K)) {W : Type*} [AddCommGroup W] [Module K W]
    (ρ : Representation K G W) : Prop where
  finiteDimensional : FiniteDimensional K W
  coeff_mem : ∀ (f : Module.Dual K W) (w : W), (fun g => f (ρ g w)) ∈ A

namespace HasCoeffsIn

variable {A : Subalgebra K (G → K)}
variable {W : Type*} [AddCommGroup W] [Module K W] {ρ : Representation K G W}
variable {V : Type*} [AddCommGroup V] [Module K V] {σ : Representation K G V}

theorem mono {B : Subalgebra K (G → K)} (h : HasCoeffsIn A ρ) (hAB : A ≤ B) :
    HasCoeffsIn B ρ :=
  ⟨h.finiteDimensional, fun f w => hAB (h.coeff_mem f w)⟩

theorem toMatrix_mem (h : HasCoeffsIn A ρ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K W) (i j : ι) : (fun g => LinearMap.toMatrix b b (ρ g) i j) ∈ A := by
  simpa [LinearMap.toMatrix_apply] using h.coeff_mem (b.coord i) (b j)

end HasCoeffsIn

variable {A : Subalgebra K (G → K)}
variable {W : Type*} [AddCommGroup W] [Module K W] {ρ : Representation K G W}
variable {V : Type*} [AddCommGroup V] [Module K V] {σ : Representation K G V}

/-- A matrix coefficient expanded in a basis. -/
theorem coeff_eq_sum_toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K W)
    (f : Module.Dual K W) (w : W) (g : G) :
    f (ρ g w) = ∑ i, ∑ j, (f (b i) * b.repr w j) * LinearMap.toMatrix b b (ρ g) i j := by
  conv_lhs => rw [← b.sum_repr w]
  simp only [map_sum, map_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [← b.sum_repr (ρ g (b j))]
  simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum, LinearMap.toMatrix_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Basis criterion**: a representation has coefficients in `A` exactly when the entries of its
matrices against one finite basis do. -/
theorem hasCoeffsIn_iff_toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K W) :
    HasCoeffsIn A ρ ↔ ∀ i j, (fun g => LinearMap.toMatrix b b (ρ g) i j) ∈ A := by
  refine ⟨fun h => h.toMatrix_mem b, fun h => ⟨Module.Finite.of_basis b,
    fun f w => ?_⟩⟩
  have : (fun g => f (ρ g w)) =
      ∑ i, ∑ j, (f (b i) * b.repr w j) • fun g => LinearMap.toMatrix b b (ρ g) i j := by
    funext g
    simp only [coeff_eq_sum_toMatrix b f w g, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [this]
  exact Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ =>
    Subalgebra.smul_mem _ (h i j) _

/-- The source of an injective intertwining map into a representation with coefficients in `A`
has coefficients in `A`. In particular this applies to subrepresentations. -/
theorem HasCoeffsIn.of_injective (h : HasCoeffsIn A ρ) (φ : σ.IntertwiningMap ρ)
    (hφ : Function.Injective φ) : HasCoeffsIn A σ := by
  have := h.finiteDimensional
  have : FiniteDimensional K V := FiniteDimensional.of_injective φ.toLinearMap hφ
  refine ⟨inferInstance, fun f v => ?_⟩
  obtain ⟨ψ, hψ⟩ := φ.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hφ)
  have : (fun g => f (σ g v)) = fun g => (f ∘ₗ ψ) (ρ g (φ v)) := by
    funext g
    rw [← φ.isIntertwining, LinearMap.comp_apply]
    change f (σ g v) = f (ψ (φ.toLinearMap (σ g v)))
    rw [← LinearMap.comp_apply ψ, hψ, LinearMap.id_apply]
  rw [this]
  exact h.coeff_mem _ _

/-- The target of a surjective intertwining map out of a representation with coefficients in `A`
has coefficients in `A`. In particular this applies to quotients. -/
theorem HasCoeffsIn.of_surjective (h : HasCoeffsIn A ρ) (φ : ρ.IntertwiningMap σ)
    (hφ : Function.Surjective φ) : HasCoeffsIn A σ := by
  have := h.finiteDimensional
  have : FiniteDimensional K V := Module.Finite.of_surjective φ.toLinearMap hφ
  refine ⟨inferInstance, fun f v => ?_⟩
  obtain ⟨w, rfl⟩ := hφ v
  have : (fun g => f (σ g (φ w))) = fun g => (f ∘ₗ φ.toLinearMap) (ρ g w) := by
    funext g
    rw [← φ.isIntertwining]
    rfl
  rw [this]
  exact h.coeff_mem _ _

/-- Equivalent representations have coefficients in the same algebras. -/
theorem HasCoeffsIn.of_equiv (h : HasCoeffsIn A ρ) (e : ρ.Equiv σ) : HasCoeffsIn A σ :=
  h.of_surjective e.toIntertwiningMap e.toLinearEquiv.surjective

/-- A subrepresentation of a representation with coefficients in `A` has coefficients in `A`. -/
theorem HasCoeffsIn.subrepresentation (h : HasCoeffsIn A ρ) (U : Subrepresentation ρ) :
    HasCoeffsIn A U.toRepresentation :=
  h.of_injective ⟨U.toSubmodule.subtype, fun _ => rfl⟩ Subtype.val_injective

/-- A quotient of a representation with coefficients in `A` has coefficients in `A`. -/
theorem HasCoeffsIn.quotient (h : HasCoeffsIn A ρ) (U : Subrepresentation ρ) :
    HasCoeffsIn A U.quotient :=
  h.of_surjective ⟨U.toSubmodule.mkQ, fun _ => rfl⟩ U.toSubmodule.mkQ_surjective

/-- The product of two representations with coefficients in `A` has coefficients in `A`. -/
theorem HasCoeffsIn.prod (hρ : HasCoeffsIn A ρ) (hσ : HasCoeffsIn A σ) :
    HasCoeffsIn A (ρ.prod σ) := by
  have := hρ.finiteDimensional
  have := hσ.finiteDimensional
  refine ⟨inferInstance, fun f x => ?_⟩
  have : (fun g => f ((ρ.prod σ) g x)) =
      (fun g => (f ∘ₗ LinearMap.inl K W V) (ρ g x.1)) +
        fun g => (f ∘ₗ LinearMap.inr K W V) (σ g x.2) := by
    funext g
    have hx : (ρ.prod σ) g x = (ρ g x.1, 0) + (0, σ g x.2) := by
      rw [Prod.mk_add_mk, add_zero, zero_add]
      rfl
    rw [hx, map_add]
    rfl
  rw [this]
  exact add_mem (hρ.coeff_mem _ _) (hσ.coeff_mem _ _)

/-- The tensor product of two representations with coefficients in `A` has coefficients in
`A`. -/
theorem HasCoeffsIn.tprod (hρ : HasCoeffsIn A ρ) (hσ : HasCoeffsIn A σ) :
    HasCoeffsIn A (ρ.tprod σ) := by
  have := hρ.finiteDimensional
  have := hσ.finiteDimensional
  classical
  let b := Module.finBasis K W
  let c := Module.finBasis K V
  rw [hasCoeffsIn_iff_toMatrix (b.tensorProduct c)]
  exact TauCeti.Representation.toMatrix_tprod_mem A b c (hρ.toMatrix_mem b) (hσ.toMatrix_mem c)

/-- Restriction along a monoid homomorphism `φ : H →* G` keeps the coefficients polynomial,
as soon as `f ∘ φ ∈ B` for every `f ∈ A`. -/
theorem HasCoeffsIn.comp {H : Type*} [Monoid H] {B : Subalgebra K (H → K)} (h : HasCoeffsIn A ρ)
    (φ : H →* G) (hφ : ∀ f ∈ A, f ∘ φ ∈ B) : HasCoeffsIn B (ρ.comp φ) :=
  ⟨h.finiteDimensional, fun f w => hφ _ (h.coeff_mem f w)⟩

/-! ### Restriction along homomorphisms -/

section Comp

variable {H : Type*} [Monoid H]

/-- An equivalence of representations restricts to an equivalence along any monoid
homomorphism. -/
def equivComp (e : ρ.Equiv σ) (φ : H →* G) :
    Representation.Equiv (ρ.comp φ) (σ.comp φ) :=
  .mk e.toLinearEquiv fun h => e.isIntertwining' (φ h)

theorem prod_comp (φ : H →* G) :
    (ρ.prod σ).comp φ = Representation.prod (ρ.comp φ) (σ.comp φ) :=
  MonoidHom.ext fun _ => rfl

theorem tprod_comp (φ : H →* G) :
    (ρ.tprod σ).comp φ = Representation.tprod (ρ.comp φ) (σ.comp φ) :=
  MonoidHom.ext fun _ => rfl

end Comp

/-- A trivial representation on a finite-dimensional space has coefficients in every algebra of
functions. -/
theorem HasCoeffsIn.trivial [FiniteDimensional K W] :
    HasCoeffsIn A (Representation.trivial K G W) :=
  ⟨inferInstance, fun f w => by
    simp only [Representation.trivial_apply]
    exact Subalgebra.algebraMap_mem A (f w)⟩

/-! ### Tensor products of families -/

section PiTensor

variable {ι : Type*} {V' : ι → Type*} [∀ i, AddCommGroup (V' i)] [∀ i, Module K (V' i)]

/-- The tensor product `⨂ᵢ ρᵢ` of a finite family of representations of the same monoid: `g`
acts by `⨂ᵢ ρᵢ(g)`. -/
def piTensor (ρ' : (i : ι) → Representation K G (V' i)) :
    Representation K G (PiTensorProduct K V') :=
  PiTensorProduct.mapMonoidHom.comp (MonoidHom.pi ρ')

theorem piTensor_tprod (ρ' : (i : ι) → Representation K G (V' i)) (g : G)
    (v : (i : ι) → V' i) :
    piTensor ρ' g (PiTensorProduct.tprod K v) =
      PiTensorProduct.tprod K fun i => ρ' i g (v i) := by
  simp [piTensor, PiTensorProduct.mapMonoidHom, PiTensorProduct.map_tprod]

/-- Against the product basis, a matrix entry of `⨂ᵢ ρᵢ(g)` is the product of the matrix entries
of the factors. -/
theorem toMatrix_piTensor [Fintype ι] [DecidableEq ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]
    [∀ i, DecidableEq (κ i)]
    (b : (i : ι) → Basis (κ i) K (V' i)) (ρ' : (i : ι) → Representation K G (V' i)) (g : G)
    (x y : (i : ι) → κ i) :
    LinearMap.toMatrix (Basis.piTensorProduct b) (Basis.piTensorProduct b) (piTensor ρ' g) x
        y = ∏ i, LinearMap.toMatrix (b i) (b i) (ρ' i g) (x i) (y i) := by
  rw [LinearMap.toMatrix_apply, Basis.piTensorProduct_apply, piTensor_tprod,
    Basis.piTensorProduct_repr_tprod_apply]
  simp [LinearMap.toMatrix_apply]

/-- The tensor product of a finite family of representations with coefficients in `A` has
coefficients in `A`. -/
theorem HasCoeffsIn.piTensor [Fintype ι] [DecidableEq ι]
    {ρ' : (i : ι) → Representation K G (V' i)} (h : ∀ i, HasCoeffsIn A (ρ' i)) :
    HasCoeffsIn A (GLRep.piTensor ρ') := by
  have := fun i => (h i).finiteDimensional
  let b := fun i => Module.finBasis K (V' i)
  rw [hasCoeffsIn_iff_toMatrix (Basis.piTensorProduct b)]
  intro x y
  have : (fun g => LinearMap.toMatrix (Basis.piTensorProduct b) (Basis.piTensorProduct b)
      (GLRep.piTensor ρ' g) x y) =
      ∏ i, fun g => LinearMap.toMatrix (b i) (b i) (ρ' i g) (x i) (y i) := by
    funext g
    rw [toMatrix_piTensor, Finset.prod_apply]
  rw [this]
  exact prod_mem fun i _ => (h i).toMatrix_mem (b i) _ _

end PiTensor

/-! ### Polynomial representations -/

section Polynomial

variable (K) in
/-- The polynomial functions on `GL_n(K)`: polynomials in the matrix entries. -/
abbrev glPolynomialFunctions (n : ℕ) : Subalgebra K (GL (Fin n) K → K) :=
  coordFunctions K (glCoord K n)

variable (K) in
/-- The polynomial functions on the Levi group `∏_p GL_{d_p}(K)`: polynomials in the matrix
entries of all blocks. -/
abbrev leviPolynomialFunctions {s : ℕ} (d : Fin s → ℕ) : Subalgebra K (LeviGroup K d → K) :=
  coordFunctions K (leviCoord K d)

/-- A representation of `GL_n(K)` is **polynomial** when it is finite-dimensional and its matrix
coefficients are polynomials in the matrix entries. -/
abbrev IsPolynomialRep {n : ℕ} (ρ : Representation K (GL (Fin n) K) W) : Prop :=
  HasCoeffsIn (glPolynomialFunctions K n) ρ

/-- A representation of the Levi group `∏_p GL_{d_p}(K)` is **polynomial** when it is
finite-dimensional and its matrix coefficients are polynomials in the matrix entries of the
blocks. -/
abbrev IsPolynomialLeviRep {s : ℕ} {d : Fin s → ℕ} (ρ : Representation K (LeviGroup K d) W) :
    Prop :=
  HasCoeffsIn (leviPolynomialFunctions K d) ρ

end Polynomial

end

end GLRep
