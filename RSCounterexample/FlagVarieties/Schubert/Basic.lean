import RSCounterexample.FlagVarieties.Flag.Action
import RSCounterexample.FlagVarieties.LineBundle.Model
import RSCounterexample.TypeA.Permutations.Bruhat
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Schubert varieties

Over a commutative ring `R`:

* `FlagVarieties.BorelScheme R n`: the Borel subgroup scheme `B = Spec 𝒪(B)` of upper triangular
  matrices, with its closed immersion `borelInclusion` into `GLₙ`.
* `FlagVarieties.permFlag R n w`: the `R`-point `ẇE•` of `Flₙ`, the flag with
  `Vⱼ = span(e_{w(0)}, …, e_{w(j-1)})`; it is `π(ẇ)` for the permutation matrix `ẇ eᵢ = e_{w(i)}`.
* `FlagVarieties.schubertOrbitMap R n w : B ⟶ Flₙ`, `b ↦ b · ẇE•`.
* **`FlagVarieties.schubertVariety R n w`**: the Schubert variety `X_w`, defined as the
  scheme-theoretic image of `schubertOrbitMap`, i.e. the closure of `B ẇ B/B` with its reduced
  structure (when `R` is reduced).
* `FlagVarieties.schubertUnion R n S`: the scheme-theoretic union `X_S = ⋃_{w ∈ S} X_w`, the
  infimum of the ideal sheaves.
* `FlagVarieties.schubertBoundary R n σ`: the boundary `∂X_σ = ⋃_{τ <ᴮ σ} X_τ`, for the strong
  Bruhat order `≤ᴮ` of `Schubert.FinPermutation`.

All of these are ideal sheaves on `Flₙ` (`Scheme.IdealSheafData`); the closed subschemes are
`I.subscheme` with the closed immersion `I.subschemeι`.
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Foundations Foundations.QuotientCharts

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

/-! ### The Borel subgroup scheme -/

/-- The Borel subgroup scheme `B ⊆ GLₙ` of upper triangular matrices, `B = Spec 𝒪(B)`. -/
abbrev BorelScheme : Scheme.{u} :=
  Spec (CommRingCat.of (BorelCoord R n))

/-- The structure morphism `B ⟶ Spec R`. -/
abbrev BorelScheme.toSpec : BorelScheme R n ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (BorelCoord R n)))

/-- The closed immersion `B ⟶ GLₙ`. -/
def borelInclusion : BorelScheme R n ⟶ GLScheme R n :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (borelCoordIdeal R n))) ≫
    (TauCeti.GeneralLinear.groupSchemeSpecIso R n).inv

@[reassoc] theorem borelInclusion_toSpec :
    borelInclusion R n ≫ (GLOver R n).hom = BorelScheme.toSpec R n := by
  rw [borelInclusion, Category.assoc, TauCeti.GeneralLinear.groupScheme_X_hom,
    Iso.inv_hom_id_assoc, BorelScheme.toSpec, ← Spec.map_comp]
  rfl

/-! ### Orbit maps of `R`-points -/

namespace FlagScheme

variable {R n}

/-- The orbit map `GLₙ ⟶ Flₙ`, `g ↦ g · x`, of an `R`-point `x` of `Flₙ` over `Spec R`. -/
def orbitMapAt (x : Spec (CommRingCat.of R) ⟶ FlagScheme R n) (hx : x ≫ toSpec R n = 𝟙 _) :
    GLScheme R n ⟶ FlagScheme R n :=
  pullback.lift (𝟙 _) ((GLOver R n).hom ≫ x) (by simp [hx]) ≫ action R n

theorem orbitMap_eq_orbitMapAt :
    orbitMap R n = orbitMapAt (standardFlag R n) standardFlag_toSpec := rfl

/-- On points, the orbit map of the `R`-point of a flag `P₀` sends `g` to `g · P₀`. -/
theorem orbitMapAt_point {A : Type u} [CommRing A] [Algebra R A] (P₀ : CoordinateFlag R n)
    (hx : ofRingFlag R P₀ ≫ toSpec R n = 𝟙 _)
    (k : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] A) :
    GLScheme.point R n k ≫ orbitMapAt (ofRingFlag R P₀) hx =
      ofRingFlag R ((Foundations.QuotientCharts.coordinateRingFlagBaseChange (B := A) P₀).transport
        (GLScheme.pointEquiv R n k)) := by
  rw [← action_point]
  unfold orbitMapAt
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc,
      generalLinearGroupPoint_toSpec, ofRingFlag_baseChange]

end FlagScheme

/-! ### Permutation flags -/

/-- The flag `ẇE•` of `Aⁿ`: `Vⱼ = span(e_{w(0)}, …, e_{w(j-1)})`. -/
def permRingFlag (w : Equiv.Perm (Fin n)) (A : Type u) [CommRing A] : CoordinateFlag A n :=
  RingFlag.ofBasis ((Pi.basisFun A (Fin n)).reindex w.symm)

theorem permRingFlag_step (w : Equiv.Perm (Fin n)) (A : Type u) [CommRing A] (j : Fin (n + 1)) :
    ((permRingFlag n w A).step j).toSubmodule =
      Submodule.span A ((fun i => Pi.single (w i) (1 : A)) '' {i | i.val < j.val}) := by
  rw [permRingFlag, RingFlag.ofBasis_step_span]
  congr 1
  ext x
  simp [Module.Basis.reindex_apply, Pi.basisFun_apply]

theorem permRingFlag_baseChange (w : Equiv.Perm (Fin n)) (A B : Type u) [CommRing A]
    [CommRing B] [Algebra A B] :
    Foundations.QuotientCharts.coordinateRingFlagBaseChange (B := B) (permRingFlag n w A) =
      permRingFlag n w B := by
  unfold permRingFlag
  rw [Foundations.QuotientCharts.coordinateRingFlagBaseChange_ofBasis]
  congr 1
  apply Module.Basis.eq_of_apply_eq
  intro i
  funext j
  rw [Foundations.QuotientCharts.coordinateBasisBaseChange_apply]
  simp only [Module.Basis.reindex_apply, Equiv.symm_symm, Pi.basisFun_apply]
  rcases eq_or_ne j (w i) with rfl | h
  · simp
  · simp [h]

/-- The `R`-point `ẇE•` of `Flₙ`. -/
def permFlag (w : Equiv.Perm (Fin n)) : Spec (CommRingCat.of R) ⟶ FlagScheme R n :=
  FlagScheme.ofRingFlag R (permRingFlag n w R)

@[reassoc (attr := simp)] theorem permFlag_toSpec (w : Equiv.Perm (Fin n)) :
    permFlag R n w ≫ FlagScheme.toSpec R n = 𝟙 _ := by
  rw [permFlag, FlagScheme.ofRingFlag_toSpec, Algebra.algebraMap_self, CommRingCat.ofHom_id,
    Spec.map_id]

/-! ### Schubert varieties -/

/-- The orbit morphism `B ⟶ Flₙ`, `b ↦ b · ẇE•`. -/
def schubertOrbitMap (w : Equiv.Perm (Fin n)) : BorelScheme R n ⟶ FlagScheme R n :=
  borelInclusion R n ≫ FlagScheme.orbitMapAt (permFlag R n w) (permFlag_toSpec R n w)

/-- **The Schubert variety `X_w`**.

It is the scheme-theoretic image of the orbit morphism `B ⟶ Flₙ`, `b ↦ b · ẇE•`, i.e. the closed
subscheme of `Flₙ` cut out by the largest quasi-coherent ideal sheaf killed by the orbit morphism.
Topologically it is the closure of the `B`-orbit `B ẇ B / B`; since `B` is reduced when `R` is,
it carries the reduced structure. As an ideal sheaf on `Flₙ`; the closed subscheme is
`(schubertVariety R n w).subscheme`. -/
def schubertVariety (w : Equiv.Perm (Fin n)) : (FlagScheme R n).IdealSheafData :=
  (schubertOrbitMap R n w).ker

/-- The scheme-theoretic union `X_S = ⋃_{w ∈ S} X_w` of Schubert varieties: the infimum of their
ideal sheaves. -/
def schubertUnion (S : Finset (Equiv.Perm (Fin n))) : (FlagScheme R n).IdealSheafData :=
  ⨅ w ∈ S, schubertVariety R n w

open Classical in
/-- The Schubert boundary `∂X_σ = ⋃_{τ <ᴮ σ} X_τ`, for the strong Bruhat order. -/
def schubertBoundary (σ : Equiv.Perm (Fin n)) : (FlagScheme R n).IdealSheafData :=
  schubertUnion R n (Finset.univ.filter fun τ => Schubert.FinPermutation.StrongBruhatLE τ σ ∧ τ ≠ σ)

theorem schubertUnion_singleton (w : Equiv.Perm (Fin n)) :
    schubertUnion R n {w} = schubertVariety R n w := by
  simp [schubertUnion]

theorem schubertUnion_union (S T : Finset (Equiv.Perm (Fin n))) :
    schubertUnion R n (S ∪ T) = schubertUnion R n S ⊓ schubertUnion R n T := by
  simp only [schubertUnion]
  exact Finset.iInf_union

end FlagVarieties
