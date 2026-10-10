import RSCounterexample.FlagVarieties.LineBundle.Descent
import TauCeti.Algebra.Category.ModuleCat.Sheaf.LocalIsomorphism

/-!
# Isomorphisms of sheaves of modules from local data

* `FlagVarieties.bijective_of_bases`: a linear map between two free modules of rank one, sending
  some element `m` to a basis vector, is bijective once `m` is (a multiple of) a basis vector of
  the source.
* `FlagVarieties.isIso_of_forall_bijective`: a morphism of `𝒪_X`-modules is an isomorphism if it is
  bijective on all sections over the opens contained in the members of an open cover.
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v

/-- A linear map `Φ : M → N` between free modules of rank one over `A` (with bases `g`, `s`) is
bijective if it sends some `m ∈ M` to the basis vector `s`. -/
theorem bijective_of_bases {A : Type v} [CommRing A] {M N : Type v} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (Φ : M →ₗ[A] N) {g : M} {s : N} (m : M)
    (hg : Function.Bijective (fun a : A => a • g)) (hs : Function.Bijective (fun a : A => a • s))
    (hm : Φ m = s) : Function.Bijective Φ := by
  obtain ⟨c, hc⟩ := hg.2 m
  obtain ⟨d, hd⟩ := hs.2 (Φ g)
  simp only at hc hd
  have hcd : c * d = 1 := by
    apply hs.1
    change (c * d) • s = (1 : A) • s
    rw [one_smul, mul_smul, hd, ← map_smul, hc, hm]
  have hΦ : ∀ b : A, Φ (b • g) = (b * d) • s := fun b => by
    rw [map_smul, ← hd, smul_smul]
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := hg.2 x
    obtain ⟨b, rfl⟩ := hg.2 y
    simp only [hΦ] at hxy
    have h := congrArg (· * c) (hs.1 hxy)
    simp only [mul_assoc, mul_comm d c, hcd, mul_one] at h
    rw [h]
  · intro y
    obtain ⟨a, rfl⟩ := hs.2 y
    refine ⟨(a * c) • g, ?_⟩
    simp only [hΦ, mul_assoc, hcd, mul_one]

/-- **A morphism of `𝒪_X`-modules is an isomorphism if it is bijective on all sections over the
opens inside the members of an open cover.** -/
theorem isIso_of_forall_bijective {X : Scheme.{u}} {M N : X.Modules} (Φ : M ⟶ N) {ι : Type u}
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (h : ∀ i (W : X.Opens), W ≤ U i → Function.Bijective (Φ.app W)) : IsIso Φ := by
  refine SheafOfModules.isIso_of_coversTop ((Opens.coversTop_iff _ U).mpr hU) Φ fun i => ?_
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _),
    NatTrans.isIso_iff_isIso_app]
  intro Y
  rw [ConcreteCategory.isIso_iff_bijective]
  exact h i Y.unop.left (leOfHom Y.unop.hom)

/-- The structure sheaf `𝒪_X` as an `𝒪_X`-module. -/
abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- The morphism `𝒪_X ⟶ M`, `1 ↦ s`, given by a global section `s`. -/
def unitHomOfSection {X : Scheme.{u}} (M : X.Modules) (s : Γ(M, ⊤)) :
    unitModule X ⟶ M :=
  M.unitHomEquiv.symm (PresheafOfModules.sectionsMk
    (fun W => (M.presheaf.map (homOfLE le_top : W.unop ⟶ ⊤).op).hom s)
    (fun W W' f => by
      change (M.presheaf.map f).hom ((M.presheaf.map _).hom s) = _
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl))

theorem unitHomOfSection_app {X : Scheme.{u}} (M : X.Modules) (s : Γ(M, ⊤)) (W : X.Opens)
    (a : Γ(X, W)) :
    ((unitHomOfSection M s).app W).hom a =
      a • (M.presheaf.map (homOfLE le_top : W ⟶ ⊤).op).hom s :=
  rfl

/-- `𝒪_X ⟶ M`, `1 ↦ s`, is an isomorphism if every section of `M` is uniquely a multiple of the
restriction of `s`. -/
theorem isIso_unitHomOfSection {X : Scheme.{u}} (M : X.Modules) (s : Γ(M, ⊤))
    (h : ∀ W : X.Opens, Function.Bijective
      (fun a : Γ(X, W) => a • (M.presheaf.map (homOfLE le_top : W ⟶ ⊤).op).hom s)) :
    IsIso (unitHomOfSection M s) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  rw [ConcreteCategory.isIso_iff_bijective]
  exact h W

end FlagVarieties
