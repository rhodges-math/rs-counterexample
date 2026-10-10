import RSCounterexample.FlagVarieties.Foundations.Schemes.AffineQuotientProjectiveLine
import RSCounterexample.FlagVarieties.Foundations.Schemes.QuotientPairIsomorphism

/-!
# Affine quotient morphisms over a fixed coefficient ring

The relative constructor uses exactly the previously constructed principal
cover and section frames. Quotient-module isomorphism invariance
allows different automatically selected covers on the two modules.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientPair

open AlgebraicGeometry CategoryTheory TensorProduct TopologicalSpace

universe u

variable {A : Type u} [CommRing A] {R : CommRingCat.{u}}
  (M : ModuleCat.{u} R) [Module.Finite R M] [Module.Projective R M]
  (hrank : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = 1)

attribute [local instance] openAlgebra principalOpenAlgebra principalOpenSectionModule

/-- The same affine quotient construction, with a fixed base for the target projective line. -/
def fromFiniteProjectivePairOver (φ : A →+* R)
    (q : R × R →ₗ[R] M) (hq : Function.Surjective q) :
    Spec R ⟶ ProjectiveLine.scheme A :=
  fromFrames (affineGlobalPair M q) (affineGlobalPair_surjective M q hq)
    (affineModuleOnFrame M hrank) ((algebraMap R Γ(Spec R, ⊤)).comp φ)
    (affineFrameCover M hrank)

@[simp] theorem fromFiniteProjectivePairOver_id
    (q : R × R →ₗ[R] M) (hq : Function.Surjective q) :
    fromFiniteProjectivePairOver M hrank (RingHom.id R) q hq =
      fromFiniteProjectivePair M hrank q hq := rfl

theorem fromFiniteProjectivePairOver_toSpec (φ : A →+* R)
    (q : R × R →ₗ[R] M) (hq : Function.Surjective q) :
    fromFiniteProjectivePairOver M hrank φ q hq ≫ ProjectiveLine.toSpec A =
      Spec.map (CommRingCat.ofHom φ) := by
  rw [fromFiniteProjectivePairOver, fromFrames_toSpec]
  simp only [CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc]
  change ((Spec R).toSpecΓ ≫ Spec.map (Scheme.ΓSpecIso R).inv) ≫ _ = _
  rw [toSpecΓ_SpecMap_ΓSpecIso_inv, Category.id_comp]

variable {M} {N : ModuleCat.{u} R} [Module.Finite R N] [Module.Projective R N]
  (hrankN : ∀ p : PrimeSpectrum R, Module.rankAtStalk N p = 1)

/-- The affine morphism respects an isomorphism of ordered quotient modules. -/
theorem fromFiniteProjectivePairOver_quotient_equiv
    (φ : A →+* R) (q : R × R →ₗ[R] M) (hq : Function.Surjective q)
    (q' : R × R →ₗ[R] N) (hq' : Function.Surjective q')
    (e : M ≃ₗ[R] N) (he : ∀ x, e (q x) = q' x) :
    fromFiniteProjectivePairOver M hrank φ q hq =
      fromFiniteProjectivePairOver N hrankN φ q' hq' := by
  unfold fromFiniteProjectivePairOver
  apply fromFrames_quotient_equiv _ _ _ _ (e.baseChange R Γ(Spec R, ⊤) M N)
  rintro ⟨a, b⟩
  simp only [affineGlobalPair_apply, map_add, map_smul, LinearEquiv.baseChange_tmul, he]

theorem fromFiniteProjectivePair_quotient_equiv
    (q : R × R →ₗ[R] M) (hq : Function.Surjective q)
    (q' : R × R →ₗ[R] N) (hq' : Function.Surjective q')
    (e : M ≃ₗ[R] N) (he : ∀ x, e (q x) = q' x) :
    fromFiniteProjectivePair M hrank q hq = fromFiniteProjectivePair N hrankN q' hq' :=
  fromFiniteProjectivePairOver_quotient_equiv hrank hrankN (RingHom.id R) q hq q' hq' e he

end FlagVarieties.Foundations.QuotientPair
