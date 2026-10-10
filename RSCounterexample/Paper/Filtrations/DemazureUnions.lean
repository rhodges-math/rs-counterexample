import RSCounterexample.Paper.BModules.Filtrations
import RSCounterexample.Paper.Representation.FlagTorus
import RSCounterexample.Paper.Representation.FlagFinite
import RSCounterexample.Paper.JosephPolo.BruhatMonotonicity
import RSCounterexample.Paper.TorusCharacterTransport

/-!
# Sums of Demazure modules

For a column shape `m` (the dominant weight `λ = shapeWeight m`) and a permutation `w`, REL's
`flagDemazure m w` is the Demazure module `D_w(λ)`: the `U(𝔫⁺)`-cyclic span of the extremal
flag polynomial `extremalFlag m w`. For a finite set `S` of permutations,

  `demazureUnion m S = Σ_{w ∈ S} D_w(λ)`

is the sum of the Demazure modules indexed by `S`. Its dual is the space of sections over the
union of Schubert varieties `⋃_{w ∈ S} X_w` (see `Filtrations.SectionModules`).

This file records that these sums are finite-dimensional `B`-modules, monotone in `S` for the
Bruhat order, and that a singleton gives the Demazure module itself.
-/

namespace Schubert.RS.Filtrations

open Representation BModules FinPermutation

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

/-- A sum of invariant subspaces is invariant. -/
theorem iSup_invariant {E : Type*} [AddCommGroup E] [Module ℂ E] {ι : Sort*}
    (p : ι → Submodule ℂ E) (f : E →ₗ[ℂ] E) (h : ∀ i, ∀ x ∈ p i, f x ∈ p i) :
    ∀ x ∈ ⨆ i, p i, f x ∈ ⨆ i, p i := by
  have hle : (⨆ i, p i) ≤ (⨆ i, p i).comap f :=
    iSup_le fun i x hx => (le_iSup p i) (h i x hx)
  exact fun x hx => hle hx

theorem polynomialUpperLie_mem_flagDemazure (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    (X : upperNilpotent n) {p : MatrixPolynomial n} (hp : p ∈ flagDemazure m w) :
    polynomialUpperLie n X p ∈ flagDemazure m w := by
  have h := upperCyclic_stable (extremalFlag m w) (UniversalEnvelopingAlgebra.ι ℂ X) hp
  have he : polynomialEnveloping n (UniversalEnvelopingAlgebra.ι ℂ X) = polynomialUpperLie n X :=
    UniversalEnvelopingAlgebra.lift_ι_apply ℂ (polynomialUpperLie n) X
  rwa [he] at h

/-- The sum `Σ_{w ∈ S} D_w(λ)` of Demazure modules of shape `m`. -/
def demazureUnion (m : ColumnShape n) (S : Finset (Equiv.Perm (Fin n))) :
    Submodule ℂ (MatrixPolynomial n) :=
  ⨆ w : S, flagDemazure m w

instance demazureUnion_finite (m : ColumnShape n) (S : Finset (Equiv.Perm (Fin n))) :
    FiniteDimensional ℂ (demazureUnion m S) :=
  Submodule.finiteDimensional_iSup _

theorem flagDemazure_le_demazureUnion (m : ColumnShape n) {S : Finset (Equiv.Perm (Fin n))}
    {w : Equiv.Perm (Fin n)} (hw : w ∈ S) : flagDemazure m w ≤ demazureUnion m S :=
  le_iSup (fun w : S => flagDemazure m w) ⟨w, hw⟩

theorem demazureUnion_le_iff (m : ColumnShape n) (S : Finset (Equiv.Perm (Fin n)))
    (N : Submodule ℂ (MatrixPolynomial n)) :
    demazureUnion m S ≤ N ↔ ∀ w ∈ S, flagDemazure m w ≤ N :=
  ⟨fun h _ hw => (flagDemazure_le_demazureUnion m hw).trans h,
    fun h => iSup_le fun w => h w w.2⟩

theorem demazureUnion_singleton (m : ColumnShape n) (w : Equiv.Perm (Fin n)) :
    demazureUnion m {w} = flagDemazure m w :=
  le_antisymm ((demazureUnion_le_iff m {w} _).mpr fun v hv => by
      rw [Finset.mem_singleton.mp hv])
    (flagDemazure_le_demazureUnion m (Finset.mem_singleton_self w))

theorem demazureUnion_empty (m : ColumnShape n) : demazureUnion m ∅ = ⊥ :=
  eq_bot_iff.mpr ((demazureUnion_le_iff m ∅ ⊥).mpr fun _ hw => absurd hw (Finset.notMem_empty _))

/-- Bruhat monotonicity: if every element of `S'` lies below an element of `S`, then
`D_{S'} ≤ D_S`. This is the algebraic form of `X_{S'} ⊆ X_S`. -/
theorem demazureUnion_mono (m : ColumnShape n) {S S' : Finset (Equiv.Perm (Fin n))}
    (h : ∀ w' ∈ S', ∃ w ∈ S, w' ≤ᴮ w) : demazureUnion m S' ≤ demazureUnion m S :=
  (demazureUnion_le_iff m S' _).mpr fun w' hw' => by
    obtain ⟨w, hw, hle⟩ := h w' hw'
    exact (flagDemazure_mono m hle).trans (flagDemazure_le_demazureUnion m hw)

theorem demazureUnion_nil_mem (m : ColumnShape n) (S : Finset (Equiv.Perm (Fin n)))
    (X : upperNilpotent n) : ∀ p ∈ demazureUnion m S, polynomialUpperLie n X p ∈ demazureUnion m S :=
  iSup_invariant _ _ fun w _ hp => polynomialUpperLie_mem_flagDemazure m w X hp

theorem demazureUnion_torus_mem (m : ColumnShape n) (S : Finset (Equiv.Perm (Fin n)))
    (t : DiagonalTorus n) :
    ∀ p ∈ demazureUnion m S, polynomialTorus n t p ∈ demazureUnion m S :=
  iSup_invariant _ _ fun w _ hp => flagDemazure_torus_stable m w t hp

/-- `Σ_{w ∈ S} D_w(λ)` as a `B`-module. -/
def demazureUnionModule (m : ColumnShape n) (S : Finset (Equiv.Perm (Fin n))) : BModule n :=
  ofPolynomial (demazureUnion m S) (demazureUnion_nil_mem m S) (demazureUnion_torus_mem m S)

/-- The inclusion `D_{S'} ≤ D_S` as a homomorphism of `B`-modules. -/
def demazureUnionInclusion (m : ColumnShape n) {S S' : Finset (Equiv.Perm (Fin n))}
    (h : demazureUnion m S' ≤ demazureUnion m S) :
    (demazureUnionModule m S').Hom (demazureUnionModule m S) where
  toLinearMap := Submodule.inclusion h
  map_nil _ _ := rfl
  map_torus _ _ := rfl

theorem demazureUnionModule_weightSpace (m : ColumnShape n) (S : Finset (Equiv.Perm (Fin n)))
    (μ : Weight n) :
    (demazureUnionModule m S).weightSpace μ =
      (torusWeightSpace (polynomialTorus n) μ).comap (demazureUnion m S).subtype :=
  ofPolynomial_weightSpace _ _ _ μ

/-- The torus character of a single Demazure module transfers to the singleton sum. -/
theorem demazureUnionModule_singleton_hasTorusCharacter (m : ColumnShape n)
    (w : Equiv.Perm (Fin n)) {p : Polynomial n} (hp : HasTorusCharacter (flagTorus m w) p) :
    HasTorusCharacter (demazureUnionModule m {w}).torus p :=
  HasTorusCharacter.of_equiv hp (LinearEquiv.ofEq _ _ (demazureUnion_singleton m w).symm)
    fun _ _ => rfl

end

end Schubert.RS.Filtrations
