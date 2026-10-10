import RSCounterexample.GLRep.Borel.Filtration

/-!
# Representations with regular matrix coefficients, without finiteness

A representation `ρ` of a monoid `G` on a possibly infinite-dimensional space `W` has **local
coefficients** in an algebra `A` of functions on `G` (`GLRep.HasLocalCoeffsIn A ρ`) when every
matrix coefficient `g ↦ φ (ρ g w)`, for `φ` a linear form and `w` a vector, lies in `A`. The
condition passes to subrepresentations, quotients and restrictions, and a finite-dimensional
representation with local coefficients in `A` has coefficients in `A` in the sense of
`GLRep.HasCoeffsIn`. This is how rationality of the finite-dimensional spaces of sections of line
bundles is obtained from the regular representation on the coordinate ring.

For a representation by algebra homomorphisms on a commutative algebra `R`
(`GLRep.algebraRep`), local coefficients can be checked on generators of `R`
(`GLRep.hasLocalCoeffsIn_algebraRep`): it suffices that the orbit map `g ↦ ρ g r` of each generator
`r` is a finite sum `g ↦ ∑ᵢ cᵢ(g) • rᵢ` with `cᵢ ∈ A`, that is, lies in the range of
`GLRep.coeffTensorHom A R : A ⊗ R → (G → R)`.
-/

namespace GLRep

open Module
open scoped TensorProduct

noncomputable section

/-! ### Local coefficients -/

section General

variable {K G : Type*} [Field K] [Monoid G]
variable {W : Type*} [AddCommGroup W] [Module K W] {ρ : Representation K G W}
variable {V : Type*} [AddCommGroup V] [Module K V] {σ : Representation K G V}
variable {A : Subalgebra K (G → K)}

/-- Every matrix coefficient `g ↦ φ (ρ g w)` of `ρ` lies in the algebra of functions `A`. Unlike
`GLRep.HasCoeffsIn`, no finiteness is required. -/
def HasLocalCoeffsIn (A : Subalgebra K (G → K)) (ρ : Representation K G W) : Prop :=
  ∀ (φ : Module.Dual K W) (w : W), (fun g => φ (ρ g w)) ∈ A

theorem HasCoeffsIn.hasLocalCoeffsIn (h : HasCoeffsIn A ρ) : HasLocalCoeffsIn A ρ :=
  h.coeff_mem

namespace HasLocalCoeffsIn

/-- A finite-dimensional representation with local coefficients in `A` has coefficients in
`A`. -/
theorem hasCoeffsIn [FiniteDimensional K W] (h : HasLocalCoeffsIn A ρ) : HasCoeffsIn A ρ :=
  ⟨inferInstance, h⟩

theorem mono {B : Subalgebra K (G → K)} (h : HasLocalCoeffsIn A ρ) (hAB : A ≤ B) :
    HasLocalCoeffsIn B ρ := fun φ w => hAB (h φ w)

/-- The source of an injective intertwining map into a representation with local coefficients
in `A` has local coefficients in `A`. -/
theorem of_injective (h : HasLocalCoeffsIn A ρ) (φ : σ.IntertwiningMap ρ)
    (hφ : Function.Injective φ) : HasLocalCoeffsIn A σ := by
  intro f v
  obtain ⟨ψ, hψ⟩ := φ.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hφ)
  have : (fun g => f (σ g v)) = fun g => (f ∘ₗ ψ) (ρ g (φ v)) := by
    funext g
    rw [← φ.isIntertwining, LinearMap.comp_apply]
    change f (σ g v) = f (ψ (φ.toLinearMap (σ g v)))
    rw [← LinearMap.comp_apply ψ, hψ, LinearMap.id_apply]
  rw [this]
  exact h _ _

/-- The target of a surjective intertwining map out of a representation with local coefficients
in `A` has local coefficients in `A`. -/
theorem of_surjective (h : HasLocalCoeffsIn A ρ) (φ : ρ.IntertwiningMap σ)
    (hφ : Function.Surjective φ) : HasLocalCoeffsIn A σ := by
  intro f v
  obtain ⟨w, rfl⟩ := hφ v
  have : (fun g => f (σ g (φ w))) = fun g => (f ∘ₗ φ.toLinearMap) (ρ g w) := by
    funext g
    rw [← φ.isIntertwining]
    rfl
  rw [this]
  exact h _ _

theorem subrepresentation (h : HasLocalCoeffsIn A ρ) (U : Subrepresentation ρ) :
    HasLocalCoeffsIn A U.toRepresentation :=
  h.of_injective ⟨U.toSubmodule.subtype, fun _ => rfl⟩ Subtype.val_injective

theorem quotient (h : HasLocalCoeffsIn A ρ) (U : Subrepresentation ρ) :
    HasLocalCoeffsIn A U.quotient :=
  h.of_surjective ⟨U.toSubmodule.mkQ, fun _ => rfl⟩ U.toSubmodule.mkQ_surjective

theorem subquotient (h : HasLocalCoeffsIn A ρ) (U V : Subrepresentation ρ) :
    HasLocalCoeffsIn A (GLRep.subquotient U V) :=
  (h.subrepresentation V).quotient _

/-- Restriction along a monoid homomorphism `φ : H →* G`, as soon as `f ∘ φ ∈ B` for every
`f ∈ A`. -/
theorem comp {H : Type*} [Monoid H] {B : Subalgebra K (H → K)} (h : HasLocalCoeffsIn A ρ)
    (φ : H →* G) (hφ : ∀ f ∈ A, f ∘ φ ∈ B) : HasLocalCoeffsIn B (ρ.comp φ) :=
  fun f w => hφ _ (h f w)

/-- **A finite-dimensional subrepresentation of a representation with local coefficients in `A`
has coefficients in `A`.** -/
theorem hasCoeffsIn_subrepresentation (h : HasLocalCoeffsIn A ρ) (U : Subrepresentation ρ)
    [FiniteDimensional K U.toSubmodule] : HasCoeffsIn A U.toRepresentation :=
  (h.subrepresentation U).hasCoeffsIn

end HasLocalCoeffsIn

end General

/-! ### Representations by algebra homomorphisms -/

section Algebra

variable {K G : Type*} [Field K] [Monoid G] {R : Type*} [CommRing R] [Algebra K R]

/-- The representation of `G` on an algebra `R` given by a monoid homomorphism into the algebra
endomorphisms of `R`. -/
def algebraRep (ρ : G →* (R →ₐ[K] R)) : Representation K G R where
  toFun g := (ρ g).toLinearMap
  map_one' := by
    ext r
    simp
  map_mul' g h := by
    ext r
    simp

@[simp]
theorem algebraRep_apply (ρ : G →* (R →ₐ[K] R)) (g : G) (r : R) : algebraRep ρ g r = ρ g r :=
  rfl

end Algebra

section CoeffTensor

variable {K G : Type*} [Field K] (A : Subalgebra K (G → K))
variable (R : Type*) [CommRing R] [Algebra K R]

/-- The algebra homomorphism `A ⊗ R → (G → R)`, `c ⊗ r ↦ (g ↦ c(g) • r)`. Its range consists of
the finite sums `g ↦ ∑ᵢ cᵢ(g) • rᵢ` with `cᵢ ∈ A`. -/
def coeffTensorHom : A ⊗[K] R →ₐ[K] (G → R) :=
  Algebra.TensorProduct.lift ((AlgHom.compLeft (Algebra.ofId K R) G).comp A.val)
    (Pi.constAlgHom K G R) fun _ _ => Commute.all _ _

variable {A R}

theorem coeffTensorHom_tmul (c : A) (r : R) :
    coeffTensorHom A R (c ⊗ₜ r) = fun g => (c : G → K) g • r := by
  funext g
  simp [coeffTensorHom, Algebra.smul_def]

/-- The functions `g ↦ c(g) • r` with `c ∈ A` lie in the range of `coeffTensorHom`. -/
theorem smul_mem_range_coeffTensorHom {c : G → K} (hc : c ∈ A) (r : R) :
    (fun g => c g • r) ∈ (coeffTensorHom A R).range :=
  ⟨⟨c, hc⟩ ⊗ₜ r, coeffTensorHom_tmul _ r⟩

/-- The functions `g ↦ ∑ᵢ cᵢ(g) • rᵢ` with `cᵢ ∈ A` lie in the range of `coeffTensorHom`. -/
theorem sum_smul_mem_range_coeffTensorHom {ι : Type*} (s : Finset ι) (c : ι → G → K)
    (hc : ∀ i ∈ s, c i ∈ A) (r : ι → R) :
    (fun g => ∑ i ∈ s, c i g • r i) ∈ (coeffTensorHom A R).range := by
  classical
  refine ⟨∑ i ∈ s.attach, ⟨c i, hc i i.2⟩ ⊗ₜ r i, ?_⟩
  change coeffTensorHom A R _ = _
  funext g
  simp only [map_sum, Finset.sum_apply, coeffTensorHom_tmul]
  exact Finset.sum_attach s fun i => c i g • r i

/-- Composing an element of the range of `coeffTensorHom` with a linear form gives a function in
`A`. -/
theorem comp_coeffTensorHom_mem (φ : Module.Dual K R) (t : A ⊗[K] R) :
    (fun g => φ (coeffTensorHom A R t g)) ∈ A := by
  induction t with
  | tmul c r =>
    have : (fun g => φ (coeffTensorHom A R (c ⊗ₜ r) g)) = φ r • (c : G → K) := by
      funext g
      rw [coeffTensorHom_tmul, map_smul, smul_eq_mul, Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [this]
    exact A.smul_mem c.2 _
  | add x y hx hy =>
    have : (fun g => φ (coeffTensorHom A R (x + y) g)) =
        (fun g => φ (coeffTensorHom A R x g)) + fun g => φ (coeffTensorHom A R y g) := by
      funext g
      simp
    rw [this]
    exact add_mem hx hy

variable [Monoid G]

/-- The orbit map `r ↦ (g ↦ ρ g r)` of a representation by algebra homomorphisms, an algebra
homomorphism. -/
def orbitAlgHom (ρ : G →* (R →ₐ[K] R)) : R →ₐ[K] (G → R) :=
  AlgHom.pi fun g => ρ g

@[simp]
theorem orbitAlgHom_apply (ρ : G →* (R →ₐ[K] R)) (r : R) (g : G) :
    orbitAlgHom ρ r g = ρ g r :=
  rfl

/-- **Local coefficients can be checked on generators.** If the orbit map of each element of a
generating set of `R` is a finite sum `g ↦ ∑ᵢ cᵢ(g) • rᵢ` with `cᵢ ∈ A`, then every matrix
coefficient of `R` lies in `A`. -/
theorem hasLocalCoeffsIn_algebraRep (ρ : G →* (R →ₐ[K] R)) {s : Set R}
    (hs : Algebra.adjoin K s = ⊤) (h : ∀ r ∈ s, orbitAlgHom ρ r ∈ (coeffTensorHom A R).range) :
    HasLocalCoeffsIn A (algebraRep ρ) := by
  have hle : Algebra.adjoin K s ≤ (coeffTensorHom A R).range.comap (orbitAlgHom ρ) :=
    Algebra.adjoin_le h
  rw [hs] at hle
  intro φ r
  obtain ⟨t, ht⟩ := hle (Algebra.mem_top : r ∈ (⊤ : Subalgebra K R))
  have hg : ∀ g, coeffTensorHom A R t g = ρ g r := fun g => congrFun ht g
  have : (fun g => φ (algebraRep ρ g r)) = fun g => φ (coeffTensorHom A R t g) := by
    funext g
    rw [hg]
    rfl
  rw [this]
  exact comp_coeffTensorHom_mem φ t

end CoeffTensor

end

end GLRep
