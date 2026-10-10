import RSCounterexample.FlagVarieties.Foundations.Schemes.AffineSheafSections
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.LinearAlgebra.Basis.Fin

/-!
# Affine presentations of quotient sheaves on a scheme

Restriction of an epimorphism of quasicoherent sheaves to any affine open
is surjective on sections. For a quotient of the free sheaf on two
ordered generators, the affine ordered module pair is constructed using
the canonical restriction and tilde isomorphisms. No affine presentation
or surjectivity of its module map is supplied as data.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientPair

open AlgebraicGeometry CategoryTheory TensorProduct TopologicalSpace Opposite

universe u

/-- An epimorphism has surjective sections on each affine open. -/
theorem affineOpen_app_surjective {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (q : M ⟶ N) [Epi q]
    (U : X.Opens) (hU : IsAffineOpen U) : Function.Surjective (q.app U) := by
  have h := sheafGlobalMap_surjective ((Scheme.Modules.restrictFunctor hU.fromSpec).map q)
  change Function.Surjective (q.app (hU.fromSpec ''ᵁ ⊤)) at h
  have heq : hU.fromSpec ''ᵁ ⊤ = U :=
    (Scheme.Hom.image_top_eq_opensRange hU.fromSpec).trans hU.opensRange_fromSpec
  exact heq ▸ h

/-- Local freeness of the sheaves suffices; quasicoherence is derived by mathlib. -/
theorem affineOpen_app_surjective_of_locallyFree {X : Scheme.{u}} {M N : X.Modules}
    [M.IsLocallyFree] [N.IsLocallyFree] (q : M ⟶ N) [Epi q]
    (U : X.Opens) (hU : IsAffineOpen U) : Function.Surjective (q.app U) :=
  affineOpen_app_surjective q U hU

variable {X : Scheme.{u}} {R : CommRingCat.{u}} (f : Spec R ⟶ X) [IsOpenImmersion f]

/-- The standard free module presents the restriction of the free sheaf. -/
def affineRestrictedFreeIso (I : Type u) :
    tilde (ModuleCat.of R (I →₀ R)) ≅
      Scheme.Modules.restrict (SheafOfModules.free (R := X.ringCatSheaf) I) f := by
  let : CategoryTheory.Limits.PreservesColimitsOfSize.{u,u}
      (Scheme.Modules.restrictFunctor f) := inferInstance
  exact tildeFinsupp I ≪≫
    SheafOfModules.mapFreeIso (Scheme.Modules.restrictFunctor f) I
      (Scheme.Modules.restrictUnitIso f).symm

/-- The ordered index type, lifted to the universe of the scheme. -/
abbrev QuotientPairIndex : Type u := ULift.{u} (Fin 2)

/-- The order is the order `(1,0), (0,1)` of the two module generators. -/
def orderedPairFinsuppEquiv :
    (R × R) ≃ₗ[R] (QuotientPairIndex.{u} →₀ R) :=
  (Module.Basis.finTwoProd R).repr ≪≫ₗ Finsupp.domLCongr Equiv.ulift.symm

@[simp] theorem orderedPairFinsuppEquiv_first :
    orderedPairFinsuppEquiv (R := R) (1, 0) = Finsupp.single ⟨0⟩ 1 := by
  rw [orderedPairFinsuppEquiv, LinearEquiv.trans_apply,
    ← Module.Basis.finTwoProd_zero R, Module.Basis.repr_self, Finsupp.domLCongr_single]
  rfl

@[simp] theorem orderedPairFinsuppEquiv_second :
    orderedPairFinsuppEquiv (R := R) (0, 1) = Finsupp.single ⟨1⟩ 1 := by
  rw [orderedPairFinsuppEquiv, LinearEquiv.trans_apply,
    ← Module.Basis.finTwoProd_one R, Module.Basis.repr_self, Finsupp.domLCongr_single]
  rfl

/-- The trivial rank-two sheaf, with two ordered summands. -/
abbrev orderedFreeSheaf (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.free (R := X.ringCatSheaf) QuotientPairIndex.{u}

/-- A canonical identification, not a chosen source-frame hypothesis. -/
def affineOrderedFreeIso :
    tilde (ModuleCat.of R (R × R)) ≅ (orderedFreeSheaf X).restrict f :=
  (tilde.functor R).mapIso (orderedPairFinsuppEquiv (R := R)).toModuleIso ≪≫
    affineRestrictedFreeIso f QuotientPairIndex.{u}

variable {L : X.Modules}

/-- The given quotient sheaf morphism restricted to an affine chart, with its ordered source. -/
def affineQuotientSheafMap (q : orderedFreeSheaf X ⟶ L) :
    tilde (ModuleCat.of R (R × R)) ⟶ L.restrict f :=
  (affineOrderedFreeIso f).hom ≫ (Scheme.Modules.restrictFunctor f).map q

instance affineQuotientSheafMap_epi (q : orderedFreeSheaf X ⟶ L) [Epi q] :
    Epi (affineQuotientSheafMap f q) := by
  unfold affineQuotientSheafMap
  infer_instance

/-- The affine ordered quotient pair supplied by a quotient sheaf on a general scheme. -/
def affineQuotientSectionPair (q : orderedFreeSheaf X ⟶ L) :
    R × R →ₗ[R] sheafGlobalModule (L.restrict f) :=
  sheafQuotientPair (affineQuotientSheafMap f q)

/-- No sectionwise-surjectivity hypothesis is needed. -/
theorem affineQuotientSectionPair_surjective [L.IsQuasicoherent]
    (q : orderedFreeSheaf X ⟶ L) [Epi q] :
    Function.Surjective (affineQuotientSectionPair f q) :=
  sheafQuotientPair_surjective (affineQuotientSheafMap f q)

/-- This applies in particular to locally free quotient sheaves. -/
theorem affineQuotientSectionPair_surjective_of_locallyFree [L.IsLocallyFree]
    (q : orderedFreeSheaf X ⟶ L) [Epi q] :
    Function.Surjective (affineQuotientSectionPair f q) :=
  affineQuotientSectionPair_surjective f q

/-- Finite generation of affine quotient sections is a consequence of the quotient map. -/
theorem affineQuotientSections_finite [L.IsQuasicoherent]
    (q : orderedFreeSheaf X ⟶ L) [Epi q] :
    Module.Finite R (sheafGlobalModule (L.restrict f)) :=
  Module.Finite.of_surjective (affineQuotientSectionPair f q)
    (affineQuotientSectionPair_surjective f q)

/-- Tensor extension recovers the quotient sections on every smaller principal open. -/
theorem affineQuotientSectionPair_tensor [L.IsQuasicoherent]
    (q : orderedFreeSheaf X ⟶ L) (g : R) (x : R × R) :
    sheafPrincipalTensorEquiv (L.restrict f) g
        (1 ⊗ₜ[R] affineQuotientSectionPair f q x) =
      (affineQuotientSheafMap f q).app (PrimeSpectrum.basicOpen g)
        (principalToSections (ModuleCat.of R (R × R)) g x) := by
  rw [sheafPrincipalTensorEquiv_one_tmul]
  exact sheafQuotientPair_restrict (affineQuotientSheafMap f q) g x

end FlagVarieties.Foundations.QuotientPair
