import Schubert.FlagVarieties.Foundations.Schemes.AffineTildeTensor

/-!
# Affine sections of quasicoherent quotient sheaves

The affine section map of an epimorphism of quasicoherent sheaves
is surjective. The localization comparison below is built from the
restriction map of the given sheaf, using the canonical tilde counit.
Neither a module presentation nor sectionwise surjectivity is an input.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientPair

open AlgebraicGeometry CategoryTheory TensorProduct TopologicalSpace Opposite

universe u

variable {R : CommRingCat.{u}}

/-- The affine global sections, with their canonical `R`-module structure. -/
abbrev sheafGlobalModule (M : (Spec R).Modules) : ModuleCat R :=
  moduleSpecΓFunctor.obj M

/-- Affine global sections preserve an epimorphism between quasicoherent sheaves. -/
theorem sheafGlobalMap_surjective {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (q : M ⟶ N) [Epi q] :
    Function.Surjective (moduleSpecΓFunctor.map q) := by
  apply (ModuleCat.epi_iff_surjective _).mp
  apply (tilde.functor R).epi_of_epi_map
  have h : Epi ((tilde.functor R).map (moduleSpecΓFunctor.map q) ≫ N.fromTildeΓ) := by
    have hn : (tilde.functor R).map (moduleSpecΓFunctor.map q) ≫ N.fromTildeΓ =
        M.fromTildeΓ ≫ q := Scheme.Modules.fromTildeΓNatTrans.naturality q
    rw [hn]
    infer_instance
  exact (epi_comp_iff_of_isIso _ N.fromTildeΓ).mp h

/-- The global-to-principal-open restriction map. -/
def sheafToPrincipal (M : (Spec R).Modules) (f : R) :
    sheafGlobalModule M →ₗ[R] Γ(M, PrimeSpectrum.basicOpen f) :=
  ((modulesSpecToSheaf.obj M).presheaf.map (homOfLE le_top).op).hom

instance sheafToPrincipal_isLocalized (M : (Spec R).Modules) [M.IsQuasicoherent] (f : R) :
    IsLocalizedModule.Away f (sheafToPrincipal M f) :=
  (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance f

/-- Tensor extension of affine sections equals sections on a principal open. -/
def sheafPrincipalTensorEquiv (M : (Spec R).Modules) [M.IsQuasicoherent] (f : R) :
    PrincipalRing f ⊗[R] sheafGlobalModule M ≃ₗ[PrincipalRing f]
      Γ(M, PrimeSpectrum.basicOpen f) :=
  (IsLocalizedModule.isBaseChange (Submonoid.powers f) (PrincipalRing f)
    (sheafToPrincipal M f)).equiv

@[simp] theorem sheafPrincipalTensorEquiv_tmul (M : (Spec R).Modules)
    [M.IsQuasicoherent] (f : R) (a : PrincipalRing f) (m : sheafGlobalModule M) :
    sheafPrincipalTensorEquiv M f (a ⊗ₜ[R] m) = a • sheafToPrincipal M f m :=
  IsBaseChange.equiv_tmul _ a m

theorem sheafPrincipalTensorEquiv_one_tmul (M : (Spec R).Modules)
    [M.IsQuasicoherent] (f : R) (m : sheafGlobalModule M) :
    sheafPrincipalTensorEquiv M f (1 ⊗ₜ[R] m) = sheafToPrincipal M f m := by simp

/-- Tensor extension intertwines the given sheaf morphism on sections. -/
theorem sheafPrincipalTensorEquiv_map {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (q : M ⟶ N) (f : R)
    (z : PrincipalRing f ⊗[R] sheafGlobalModule M) :
    sheafPrincipalTensorEquiv N f
        ((moduleSpecΓFunctor.map q).hom.baseChange (PrincipalRing f) z) =
      q.app (PrimeSpectrum.basicOpen f) (sheafPrincipalTensorEquiv M f z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a m =>
    simp only [LinearMap.baseChange_tmul, sheafPrincipalTensorEquiv_tmul,
      Scheme.Modules.Hom.app_smul]
    congr 1
    exact (ConcreteCategory.congr_hom
      ((modulesSpecToSheaf.map q).hom.naturality (homOfLE le_top).op) m).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The comparison commutes with the restriction between principal opens. -/
theorem sheafPrincipalTensorEquiv_restrict (M : (Spec R).Modules) [M.IsQuasicoherent]
    (f : R) {g : R} (h : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f)
    (z : PrincipalRing f ⊗[R] sheafGlobalModule M) :
    sheafPrincipalTensorEquiv M g
        (TensorProduct.map (principalRestriction f h).toLinearMap LinearMap.id z) =
      M.presheaf.map (homOfLE h).op (sheafPrincipalTensorEquiv M f z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a m =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, sheafPrincipalTensorEquiv_tmul]
    rw [M.map_smul]
    congr 1
    exact (ConcreteCategory.congr_hom
      ((modulesSpecToSheaf.obj M).presheaf.map_comp
        (homOfLE (show PrimeSpectrum.basicOpen f ≤ ⊤ from le_top)).op
        (homOfLE h).op) m)
  | add x y hx hy => simp only [map_add, hx, hy]

/-- An affine quotient sheaf supplies its ordered module pair, rather than assuming it. -/
def sheafQuotientPair {N : (Spec R).Modules}
    (q : tilde (ModuleCat.of R (R × R)) ⟶ N) : R × R →ₗ[R] sheafGlobalModule N :=
  ((tilde.isoTop (ModuleCat.of R (R × R))).hom ≫ moduleSpecΓFunctor.map q).hom

theorem sheafQuotientPair_surjective {N : (Spec R).Modules} [N.IsQuasicoherent]
    (q : tilde (ModuleCat.of R (R × R)) ⟶ N) [Epi q] :
    Function.Surjective (sheafQuotientPair q) :=
  (sheafGlobalMap_surjective q).comp (ConcreteCategory.bijective_of_isIso
    (tilde.isoTop (ModuleCat.of R (R × R))).hom).surjective

/-- The ordered affine quotient sections restrict to the quotient sections. -/
theorem sheafQuotientPair_restrict {N : (Spec R).Modules}
    (q : tilde (ModuleCat.of R (R × R)) ⟶ N) (f : R) (x : R × R) :
    sheafToPrincipal N f (sheafQuotientPair q x) =
      q.app (PrimeSpectrum.basicOpen f)
        (principalToSections (ModuleCat.of R (R × R)) f x) := by
  have hn := ConcreteCategory.congr_hom
    ((modulesSpecToSheaf.map q).hom.naturality
      (homOfLE (show PrimeSpectrum.basicOpen f ≤ ⊤ from le_top)).op)
    ((tilde.toOpen (ModuleCat.of R (R × R)) ⊤) x)
  exact hn.symm

end FlagVarieties.Foundations.QuotientPair
