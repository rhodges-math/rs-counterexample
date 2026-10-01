import Schubert.GLRep.Lie.Integration
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.RepresentationTheory.Irreducible

/-!
# Polynomial representations as `gl_n`-modules

The space `W` of a polynomial representation `ρ` of `GL_n(K)`, over a field of characteristic
zero, is a module over the Lie algebra `gl_n(K) = Matrix (Fin n) (Fin n) K` through the
differential. This file names that module (`GLRep.IsPolynomialRep.LieRep`) and records the
dictionary between the two structures, consequences of `GLRep.IsPolynomialRep.adjoin_range_eq`.

* Subrepresentations of `ρ` are the Lie submodules (`GLRep.IsPolynomialRep.subrepOrderIso`), so
  `ρ` is irreducible exactly when the Lie module is (`GLRep.IsPolynomialRep.isIrreducible_iff`).
* Intertwining maps between polynomial representations are the Lie module homomorphisms
  (`GLRep.IsPolynomialRep.intertwiningEquivLieHom`). In particular two polynomial representations
  are equivalent exactly when their Lie modules are (`GLRep.IsPolynomialRep.equivOfLieModuleEquiv`).

## Main definitions

* `GLRep.IsPolynomialRep.LieRep`: the `gl_n(K)`-module of a polynomial representation.
* `GLRep.IsPolynomialRep.toLieRep`: the identity map of `W`, as a linear equivalence.
-/

namespace GLRep

open Module

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}
variable {W : Type*} [AddCommGroup W] [Module K W] {ρ : Representation K (GL (Fin n) K) W}
variable {V : Type*} [AddCommGroup V] [Module K V] {σ : Representation K (GL (Fin n) K) V}

namespace IsPolynomialRep

/-- The space of a polynomial representation, as a `gl_n(K)`-module through the differential. -/
@[nolint unusedArguments]
def LieRep (_h : IsPolynomialRep ρ) : Type _ := W

variable (h : IsPolynomialRep ρ)

instance : AddCommGroup h.LieRep := inferInstanceAs (AddCommGroup W)

instance : Module K h.LieRep := inferInstanceAs (Module K W)

instance : LieRingModule (Matrix (Fin n) (Fin n) K) h.LieRep :=
  LieRingModule.compLieHom W h.lie

instance : LieModule K (Matrix (Fin n) (Fin n) K) h.LieRep :=
  LieModule.compLieHom W h.lie

instance : FiniteDimensional K h.LieRep := h.finiteDimensional

/-- The identity map of `W`, from the representation to its Lie module. -/
def toLieRep : W ≃ₗ[K] h.LieRep := LinearEquiv.refl K W

theorem lie_toLieRep (X : Matrix (Fin n) (Fin n) K) (w : W) :
    ⁅X, h.toLieRep w⁆ = h.toLieRep (h.lie X w) := rfl

theorem toLieRep_symm_lie (X : Matrix (Fin n) (Fin n) K) (v : h.LieRep) :
    h.toLieRep.symm ⁅X, v⁆ = h.lie X (h.toLieRep.symm v) := rfl

/-- **Subrepresentations are Lie submodules.** -/
def subrepOrderIso : Subrepresentation ρ ≃o LieSubmodule K (Matrix (Fin n) (Fin n) K) h.LieRep where
  toFun U :=
    { toSubmodule := U.toSubmodule.map h.toLieRep.toLinearMap
      lie_mem := fun {X v} hv => by
        obtain ⟨w, hw, rfl⟩ := hv
        exact ⟨h.lie X w, (h.forall_rho_mem_iff U.toSubmodule).mp
          (fun g u hu => U.apply_mem_toSubmodule g hu) X w hw, rfl⟩ }
  invFun N :=
    { toSubmodule := N.toSubmodule.comap h.toLieRep.toLinearMap
      apply_mem_toSubmodule := fun g {w} hw =>
        (h.forall_rho_mem_iff (N.toSubmodule.comap h.toLieRep.toLinearMap)).mpr
          (fun X u hu => N.lie_mem (x := X) hu) g w hw }
  left_inv U := by
    apply Subrepresentation.toSubmodule_injective
    ext w
    change h.toLieRep w ∈ U.toSubmodule.map h.toLieRep.toLinearMap ↔ w ∈ U.toSubmodule
    constructor
    · rintro ⟨u, hu, huw⟩
      rwa [show u = w from h.toLieRep.injective huw] at hu
    · exact fun hw => ⟨w, hw, rfl⟩
  right_inv N := by
    apply LieSubmodule.toSubmodule_injective
    ext v
    change v ∈ (N.toSubmodule.comap h.toLieRep.toLinearMap).map h.toLieRep.toLinearMap ↔ v ∈ N
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · exact fun hv => ⟨h.toLieRep.symm v, by simpa using hv, by simp⟩
  map_rel_iff' {U U'} := by
    constructor
    · intro hle w hw
      obtain ⟨u, hu, hu'⟩ := hle ⟨w, hw, rfl⟩
      rwa [show u = w from h.toLieRep.injective hu'] at hu
    · rintro hle _ ⟨w, hw, rfl⟩
      exact ⟨w, hle hw, rfl⟩

/-- **A polynomial representation is irreducible exactly when its Lie module is.** -/
theorem isIrreducible_iff :
    ρ.IsIrreducible ↔ LieModule.IsIrreducible K (Matrix (Fin n) (Fin n) K) h.LieRep :=
  OrderIso.isSimpleOrder_iff h.subrepOrderIso

variable {h}

/-- **Intertwining maps are Lie module homomorphisms**, as a linear equivalence between the two
spaces of morphisms. -/
def intertwiningEquivLieHom (h' : IsPolynomialRep σ) :
    ρ.IntertwiningMap σ ≃ₗ[K]
      (h.LieRep →ₗ⁅K, Matrix (Fin n) (Fin n) K⁆ h'.LieRep) where
  toFun φ :=
    { toLinearMap := h'.toLieRep.toLinearMap ∘ₗ φ.toLinearMap ∘ₗ h.toLieRep.symm.toLinearMap
      map_lie' := fun {X v} => (h.map_lie_apply h' φ X (h.toLieRep.symm v)) }
  invFun f :=
    { toLinearMap := h'.toLieRep.symm.toLinearMap ∘ₗ f.toLinearMap ∘ₗ h.toLieRep.toLinearMap
      isIntertwining' := fun g => by
        have := (h.isIntertwining_iff_lie h'
          (h'.toLieRep.symm.toLinearMap ∘ₗ f.toLinearMap ∘ₗ h.toLieRep.toLinearMap)).mpr
          (fun X w => f.map_lie X (h.toLieRep w)) g
        exact LinearMap.ext this }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- `dim Hom_G(V, W) = dim Hom_{gl_n}(V, W)` for polynomial representations. -/
theorem finrank_intertwiningMap_eq (h' : IsPolynomialRep σ) :
    finrank K (ρ.IntertwiningMap σ) =
      finrank K (h.LieRep →ₗ⁅K, Matrix (Fin n) (Fin n) K⁆ h'.LieRep) :=
  (intertwiningEquivLieHom h').finrank_eq

/-- An isomorphism of Lie modules between polynomial representations is an equivalence of
representations. -/
def equivOfLieModuleEquiv (h' : IsPolynomialRep σ)
    (e : h.LieRep ≃ₗ⁅K, Matrix (Fin n) (Fin n) K⁆ h'.LieRep) : ρ.Equiv σ :=
  .mk (h.toLieRep.trans (e.toLinearEquiv.trans h'.toLieRep.symm)) fun g =>
    ((intertwiningEquivLieHom h').symm e.toLieModuleHom).isIntertwining' g

end IsPolynomialRep

end

end GLRep
