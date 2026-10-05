import Schubert.Demazure.BModules.TorusWeights
import Schubert.Demazure.PolynomialWeightSpanning
import Schubert.Demazure.Representation.PolynomialCovariance

/-!
# Algebraic modules for the upper-triangular Borel subgroup

Let `B = T ⋉ U ⊆ GL_n(ℂ)` be the upper-triangular Borel subgroup, with diagonal torus
`T = (ℂˣ)ⁿ` and unipotent radical `U`, whose Lie algebra is the strictly upper-triangular
matrices `𝔫⁺`. A finite-dimensional rational `B`-module is the same as a finite-dimensional
complex vector space with

* a representation of `𝔫⁺` (the differential of the `U`-action),
* a representation of `T` whose integral weight spaces span,
* the compatibility `t · (X · v) = (Ad t X) · (t · v)`.

`BModule n` bundles these data. `B`-submodules are the subspaces stable under both actions,
and isomorphisms are the linear isomorphisms commuting with both actions.

This file also constructs submodules, quotients, subquotients, and the `B`-module attached to
a finite-dimensional torus- and `𝔫⁺`-stable space of matrix polynomials.
-/

open Schubert

namespace Demazure.BModules

open FlagModule

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

/-! ### Restriction and quotient of Lie representations -/

section LieRestrict

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- The restriction of a Lie representation to an invariant subspace. -/
def restrictLie (φ : L →ₗ⁅ℂ⁆ Module.End ℂ E) (p : Submodule ℂ E)
    (hp : ∀ X, ∀ v ∈ p, φ X v ∈ p) : L →ₗ⁅ℂ⁆ Module.End ℂ p where
  toFun X := (φ X).restrict (hp X)
  map_add' X Y := by
    apply LinearMap.ext; intro v; apply Subtype.ext; simp
  map_smul' c X := by
    apply LinearMap.ext; intro v; apply Subtype.ext; simp
  map_lie' {X Y} := by
    apply LinearMap.ext; intro v; apply Subtype.ext
    simp [LieHom.map_lie, Ring.lie_def, Module.End.mul_apply]

@[simp] theorem restrictLie_apply (φ : L →ₗ⁅ℂ⁆ Module.End ℂ E) (p : Submodule ℂ E)
    (hp : ∀ X, ∀ v ∈ p, φ X v ∈ p) (X : L) (v : p) :
    (restrictLie φ p hp X v : E) = φ X v := rfl

/-- The Lie representation induced on the quotient by an invariant subspace. -/
def quotientLie (φ : L →ₗ⁅ℂ⁆ Module.End ℂ E) (p : Submodule ℂ E)
    (hp : ∀ X, ∀ v ∈ p, φ X v ∈ p) : L →ₗ⁅ℂ⁆ Module.End ℂ (E ⧸ p) where
  toFun X := p.mapQ p (φ X) (fun v hv => hp X v hv)
  map_add' X Y := by
    apply LinearMap.ext; intro v
    induction v using Submodule.Quotient.induction_on with
    | H v => simp
  map_smul' c X := by
    apply LinearMap.ext; intro v
    induction v using Submodule.Quotient.induction_on with
    | H v => simp
  map_lie' {X Y} := by
    apply LinearMap.ext; intro v
    induction v using Submodule.Quotient.induction_on with
    | H v => simp [LieHom.map_lie, Ring.lie_def, Module.End.mul_apply]

@[simp] theorem quotientLie_mk (φ : L →ₗ⁅ℂ⁆ Module.End ℂ E) (p : Submodule ℂ E)
    (hp : ∀ X, ∀ v ∈ p, φ X v ∈ p) (X : L) (v : E) :
    quotientLie φ p hp X (Submodule.Quotient.mk v) = Submodule.Quotient.mk (φ X v) := rfl

end LieRestrict

/-! ### `B`-modules -/

/-- A finite-dimensional algebraic module for the upper-triangular Borel subgroup of
`GL_n(ℂ)`: a representation `nil` of `𝔫⁺` and a representation `torus` of the diagonal torus,
compatible with the adjoint action, whose integral weight spaces span. -/
structure BModule (n : ℕ) where
  /-- The underlying vector space. -/
  carrier : Type
  [instAddCommGroup : AddCommGroup carrier]
  [instModule : Module ℂ carrier]
  [instFiniteDimensional : FiniteDimensional ℂ carrier]
  /-- The action of the strictly upper-triangular matrices. -/
  nil : upperNilpotent n →ₗ⁅ℂ⁆ Module.End ℂ carrier
  /-- The action of the diagonal torus. -/
  torus : DiagonalTorus n →* Module.End ℂ carrier
  torus_nil : ∀ t X v, torus t (nil X v) = nil (torusLie t X) (torus t v)
  weightDiagonal : IsWeightDiagonal torus

attribute [instance] BModule.instAddCommGroup BModule.instModule BModule.instFiniteDimensional

namespace BModule

instance : CoeSort (BModule n) Type := ⟨BModule.carrier⟩

/-- The weight space of an integral weight. -/
def weightSpace (M : BModule n) (μ : Weight n) : Submodule ℂ M := torusWeightSpace M.torus μ

/-- A homomorphism of `B`-modules. -/
structure Hom (M N : BModule n) where
  /-- The underlying linear map. -/
  toLinearMap : M →ₗ[ℂ] N
  map_nil : ∀ X v, toLinearMap (M.nil X v) = N.nil X (toLinearMap v)
  map_torus : ∀ t v, toLinearMap (M.torus t v) = N.torus t (toLinearMap v)

/-- An isomorphism of `B`-modules. -/
structure Iso (M N : BModule n) where
  /-- The underlying linear isomorphism. -/
  toLinearEquiv : M ≃ₗ[ℂ] N
  map_nil : ∀ X v, toLinearEquiv (M.nil X v) = N.nil X (toLinearEquiv v)
  map_torus : ∀ t v, toLinearEquiv (M.torus t v) = N.torus t (toLinearEquiv v)

@[inherit_doc] infixl:25 " ≃ᴮ " => Iso

namespace Iso

/-- The identity isomorphism. -/
def refl (M : BModule n) : M ≃ᴮ M where
  toLinearEquiv := LinearEquiv.refl ℂ M
  map_nil _ _ := rfl
  map_torus _ _ := rfl

/-- The inverse isomorphism. -/
def symm {M N : BModule n} (e : M ≃ᴮ N) : N ≃ᴮ M where
  toLinearEquiv := e.toLinearEquiv.symm
  map_nil X v := by
    apply e.toLinearEquiv.injective
    rw [e.map_nil, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  map_torus t v := by
    apply e.toLinearEquiv.injective
    rw [e.map_torus, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- Composition of isomorphisms. -/
def trans {M N P : BModule n} (e : M ≃ᴮ N) (f : N ≃ᴮ P) : M ≃ᴮ P where
  toLinearEquiv := e.toLinearEquiv.trans f.toLinearEquiv
  map_nil X v := by simp [e.map_nil, f.map_nil]
  map_torus t v := by simp [e.map_torus, f.map_torus]

/-- Isomorphic `B`-modules have the same weight multiplicities. -/
theorem finrank_weightSpace {M N : BModule n} (e : M ≃ᴮ N) (μ : Weight n) :
    Module.finrank ℂ (M.weightSpace μ) = Module.finrank ℂ (N.weightSpace μ) :=
  torusWeightSpace_finrank_eq M.torus N.torus e.toLinearEquiv e.map_torus μ

end Iso

end BModule

/-! ### `B`-submodules -/

/-- A `B`-submodule: a subspace stable under `𝔫⁺` and the torus. -/
@[ext]
structure BSubmodule (M : BModule n) where
  /-- The underlying subspace. -/
  toSubmodule : Submodule ℂ M
  nil_mem : ∀ X, ∀ v ∈ toSubmodule, M.nil X v ∈ toSubmodule
  torus_mem : ∀ t, ∀ v ∈ toSubmodule, M.torus t v ∈ toSubmodule

namespace BSubmodule

variable {M : BModule n}

instance : PartialOrder (BSubmodule M) :=
  PartialOrder.lift BSubmodule.toSubmodule fun _ _ h => BSubmodule.ext h

theorem le_def {S S' : BSubmodule M} : S ≤ S' ↔ S.toSubmodule ≤ S'.toSubmodule := Iff.rfl

instance : Bot (BSubmodule M) :=
  ⟨⟨⊥, fun X v hv => by rw [(Submodule.mem_bot ℂ).mp hv, map_zero]; exact Submodule.zero_mem _,
    fun t v hv => by rw [(Submodule.mem_bot ℂ).mp hv, map_zero]; exact Submodule.zero_mem _⟩⟩

instance : Top (BSubmodule M) :=
  ⟨⟨⊤, fun _ _ _ => Submodule.mem_top, fun _ _ _ => Submodule.mem_top⟩⟩

@[simp] theorem bot_toSubmodule : (⊥ : BSubmodule M).toSubmodule = ⊥ := rfl
@[simp] theorem top_toSubmodule : (⊤ : BSubmodule M).toSubmodule = ⊤ := rfl

instance : OrderBot (BSubmodule M) where
  bot_le _ := le_def.mpr bot_le

instance : OrderTop (BSubmodule M) where
  le_top _ := le_def.mpr le_top

/-- A `B`-submodule as a `B`-module. -/
def toBModule (S : BSubmodule M) : BModule n where
  carrier := S.toSubmodule
  nil := restrictLie M.nil S.toSubmodule S.nil_mem
  torus := restrictTorus M.torus S.toSubmodule S.torus_mem
  torus_nil t X v := Subtype.ext (M.torus_nil t X v)
  weightDiagonal := isWeightDiagonal_restrictTorus _ _ M.weightDiagonal

/-- The weight spaces of a `B`-submodule. -/
theorem toBModule_weightSpace (S : BSubmodule M) (μ : Weight n) :
    S.toBModule.weightSpace μ = (M.weightSpace μ).comap S.toSubmodule.subtype :=
  torusWeightSpace_restrictTorus _ _ _ μ

theorem finrank_toBModule_weightSpace (S : BSubmodule M) (μ : Weight n) :
    Module.finrank ℂ (S.toBModule.weightSpace μ) =
      Module.finrank ℂ (S.toSubmodule ⊓ M.weightSpace μ : Submodule ℂ M) := by
  rw [toBModule_weightSpace]
  exact finrank_comap_subtype S.toSubmodule _

/-- The quotient of a `B`-module by a `B`-submodule. -/
def quotient (S : BSubmodule M) : BModule n where
  carrier := M ⧸ S.toSubmodule
  nil := quotientLie M.nil S.toSubmodule S.nil_mem
  torus := quotientTorus M.torus S.toSubmodule S.torus_mem
  torus_nil t X v := by
    induction v using Submodule.Quotient.induction_on with
    | H v =>
      change Submodule.Quotient.mk (M.torus t (M.nil X v)) =
        Submodule.Quotient.mk (M.nil (torusLie t X) (M.torus t v))
      rw [M.torus_nil]
  weightDiagonal := isWeightDiagonal_quotientTorus _ _ M.weightDiagonal

/-- Additivity of weight multiplicities along a `B`-submodule. -/
theorem finrank_weightSpace_eq_add (S : BSubmodule M) (μ : Weight n) :
    Module.finrank ℂ (M.weightSpace μ) =
      Module.finrank ℂ (S.toBModule.weightSpace μ) +
        Module.finrank ℂ (S.quotient.weightSpace μ) :=
  finrank_torusWeightSpace_eq_add S.toSubmodule S.torus_mem M.weightDiagonal μ

/-- For `S ≤ S'`, the `B`-submodule of `S'` cut out by `S`. -/
def within (S S' : BSubmodule M) : BSubmodule S'.toBModule where
  toSubmodule := S.toSubmodule.comap S'.toSubmodule.subtype
  nil_mem X v hv := S.nil_mem X v.1 hv
  torus_mem t v hv := S.torus_mem t v.1 hv

/-- The subquotient `S' / S` of two `B`-submodules. -/
def subquotient (S S' : BSubmodule M) : BModule n := (S.within S').quotient

theorem finrank_within_weightSpace {S S' : BSubmodule M} (h : S ≤ S') (μ : Weight n) :
    Module.finrank ℂ ((S.within S').toBModule.weightSpace μ) =
      Module.finrank ℂ (S.toBModule.weightSpace μ) :=
  torusWeightSpace_finrank_eq _ _ (Submodule.comapSubtypeEquivOfLe (le_def.mp h))
    (fun _ _ => Subtype.ext rfl) μ

/-- Additivity of weight multiplicities for a pair of nested `B`-submodules. -/
theorem finrank_weightSpace_subquotient {S S' : BSubmodule M} (h : S ≤ S') (μ : Weight n) :
    Module.finrank ℂ (S'.toBModule.weightSpace μ) =
      Module.finrank ℂ (S.toBModule.weightSpace μ) +
        Module.finrank ℂ ((subquotient S S').weightSpace μ) := by
  rw [(S.within S').finrank_weightSpace_eq_add μ, finrank_within_weightSpace h]
  rfl

end BSubmodule

/-! ### `B`-modules of matrix polynomials -/

/-- A finite-dimensional space of matrix polynomials stable under `𝔫⁺` and the torus, as a
`B`-module. -/
def ofPolynomial (S : Submodule ℂ (MatrixPolynomial n)) [FiniteDimensional ℂ S]
    (hnil : ∀ X : upperNilpotent n, ∀ p ∈ S, polynomialUpperLie n X p ∈ S)
    (htorus : ∀ t, ∀ p ∈ S, polynomialTorus n t p ∈ S) : BModule n where
  carrier := S
  nil := restrictLie (polynomialUpperLie n) S hnil
  torus := restrictTorus (polynomialTorus n) S htorus
  torus_nil t X v := Subtype.ext (rowDerivation_torus t X.val v.val)
  weightDiagonal := by
    refine eq_top_iff.mpr ?_
    rintro ⟨p, hp⟩ -
    have hspan := polynomialWeightSpan_eq S (fun t p hp => htorus t p hp)
    rw [← hspan] at hp
    have hle : polynomialWeightSpan S ≤
        (⨆ μ : Weight n, torusWeightSpace (restrictTorus (polynomialTorus n) S htorus) μ).map
          S.subtype := by
      refine Submodule.span_le.mpr ?_
      rintro q ⟨hqS, v, hv⟩
      refine ⟨⟨q, hqS⟩, ?_, rfl⟩
      refine (le_iSup (fun μ => torusWeightSpace (restrictTorus (polynomialTorus n) S htorus) μ)
        v) ?_
      intro t
      exact Subtype.ext (hv t)
    obtain ⟨z, hz, hzp⟩ := hle hp
    have : z = ⟨p, hspan ▸ hp⟩ := Subtype.ext hzp
    rw [← this]
    exact hz

theorem ofPolynomial_weightSpace (S : Submodule ℂ (MatrixPolynomial n)) [FiniteDimensional ℂ S]
    (hnil : ∀ X : upperNilpotent n, ∀ p ∈ S, polynomialUpperLie n X p ∈ S)
    (htorus : ∀ t, ∀ p ∈ S, polynomialTorus n t p ∈ S) (μ : Weight n) :
    (ofPolynomial S hnil htorus).weightSpace μ =
      (torusWeightSpace (polynomialTorus n) μ).comap S.subtype :=
  torusWeightSpace_restrictTorus _ _ _ μ

end

end Demazure.BModules
