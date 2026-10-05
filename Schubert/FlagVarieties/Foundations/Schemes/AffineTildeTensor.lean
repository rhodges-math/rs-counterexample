import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Localization.BaseChange
import Schubert.FlagVarieties.Foundations.Schemes.QuotientPairCoordinates

/-!
# Tensor comparison for associated sheaves on principal affine opens

The comparison is induced by the `tilde.toOpen` map. It identifies
scalar extension with sections of the associated sheaf and intertwines
sheaf morphisms with tensor extension. No assertion about sections
of an arbitrary epimorphism on a nonaffine open is used.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientPair

open AlgebraicGeometry CategoryTheory TensorProduct Opposite

universe u

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (f : R)

/-- The ring of functions on the basic open set `D(f) ⊆ Spec R`. -/
abbrev PrincipalRing := Γ(Spec R, PrimeSpectrum.basicOpen f)

/-- The sections over the basic open set `D(f)` of the sheaf `M̃` associated to `M`. -/
abbrev PrincipalSections := Γ(tilde M, PrimeSpectrum.basicOpen f)

/-- The associated-sheaf section map, with its section-module codomain explicit. -/
def principalToSections : M →ₗ[R] PrincipalSections M f :=
  (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom

instance : IsLocalizedModule.Away f (principalToSections M f) :=
  inferInstanceAs (IsLocalizedModule.Away f
    (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom)

/-- The canonical tensor-to-sections comparison on `D(f)`. -/
def principalTensorEquiv :
    PrincipalRing f ⊗[R] M ≃ₗ[PrincipalRing f] PrincipalSections M f :=
  (IsLocalizedModule.isBaseChange (Submonoid.powers f) (PrincipalRing f)
    (principalToSections M f)).equiv

@[simp] theorem principalTensorEquiv_tmul (a : PrincipalRing f) (m : M) :
    principalTensorEquiv M f (a ⊗ₜ[R] m) =
      a • principalToSections M f m :=
  IsBaseChange.equiv_tmul _ a m

theorem principalTensorEquiv_one_tmul (m : M) :
    principalTensorEquiv M f (1 ⊗ₜ[R] m) =
      principalToSections M f m := by
  simp

/-- Restriction of associated sections preserves the original module element. -/
theorem principalToSections_restrict {g : R}
    (h : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) (m : M) :
    (tilde M).presheaf.map (homOfLE h).op (principalToSections M f m) =
      principalToSections M g m :=
  ConcreteCategory.congr_hom
    (tilde.toOpen_res M (PrimeSpectrum.basicOpen f) (PrimeSpectrum.basicOpen g) (homOfLE h)) m

/-- The restriction of the structure sheaf is an `R`-algebra map. -/
def principalRestriction {g : R}
    (h : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) :
    PrincipalRing f →ₐ[R] PrincipalRing g where
  __ := ((Spec R).presheaf.map (homOfLE h).op).hom
  commutes' r := by
    simp only [IsAffineOpen.algebraMap_Spec_obj, CommRingCat.hom_comp, RingHom.comp_apply]
    change (((Scheme.ΓSpecIso R).inv ≫
      (Spec R).presheaf.map (homOfLE (show PrimeSpectrum.basicOpen f ≤ ⊤ from le_top)).op ≫
      (Spec R).presheaf.map (homOfLE h).op) r) = _
    rw [← Functor.map_comp]
    rfl

/-- Naturality also holds for restrictions between principal affine opens. -/
theorem principalTensorEquiv_restrict {g : R}
    (h : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f)
    (z : PrincipalRing f ⊗[R] M) :
    principalTensorEquiv M g
        (TensorProduct.map (principalRestriction f h).toLinearMap (LinearMap.id : M →ₗ[R] M) z) =
      (tilde M).presheaf.map (homOfLE h).op (principalTensorEquiv M f z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a m =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, principalTensorEquiv_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable {M} {N : ModuleCat.{u} R}

/-- Naturality is an equality with the sheaf map on sections. -/
theorem principalTensorEquiv_map (q : M ⟶ N) (z : PrincipalRing f ⊗[R] M) :
    principalTensorEquiv N f (q.hom.baseChange (PrincipalRing f) z) =
      (tilde.map q).app (PrimeSpectrum.basicOpen f) (principalTensorEquiv M f z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a m =>
    simp only [LinearMap.baseChange_tmul, principalTensorEquiv_tmul, Scheme.Modules.Hom.app_smul]
    congr 1
    exact (ConcreteCategory.congr_hom (tilde.toOpen_map_app q (PrimeSpectrum.basicOpen f)) m).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Surjectivity of a module map implies surjectivity on every principal affine open. -/
theorem principal_map_surjective (q : M ⟶ N) (hq : Function.Surjective q) :
    Function.Surjective ((tilde.map q).app (PrimeSpectrum.basicOpen f)) := by
  intro y
  obtain ⟨z, hz⟩ := LinearMap.baseChange_surjective (PrincipalRing f) hq
    ((principalTensorEquiv N f).symm y)
  refine ⟨principalTensorEquiv M f z, ?_⟩
  rw [← principalTensorEquiv_map, hz, LinearEquiv.apply_symm_apply]

/-- In particular this is the associated quotient morphism. -/
theorem principal_quotient_surjective (K : Submodule R M) :
    Function.Surjective ((tilde.map (ModuleCat.ofHom K.mkQ)).app
      (PrimeSpectrum.basicOpen f)) :=
  principal_map_surjective f (ModuleCat.ofHom K.mkQ) K.mkQ_surjective

/-- The associated quotient map is also an epimorphism in the sheaf category. -/
theorem associated_map_epi (q : M ⟶ N) (hq : Function.Surjective q) : Epi (tilde.map q) := by
  let : Epi q := (ModuleCat.epi_iff_surjective q).mpr hq
  exact (tilde.functor R).map_epi q

/-- The canonical module quotient cocone remains a colimit in the sheaf category. -/
def associatedQuotientIsColimit (K : Submodule R M) :
    CategoryTheory.Limits.IsColimit ((tilde.functor R).mapCocone
      (ModuleCat.cokernelCocone (ModuleCat.ofHom K.subtype))) :=
  CategoryTheory.Limits.isColimitOfPreserves (tilde.functor R)
    (ModuleCat.cokernelIsColimit (ModuleCat.ofHom K.subtype))

end FlagVarieties.Foundations.QuotientPair


