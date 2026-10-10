import RSCounterexample.FlagVarieties.Modules.SectionRestriction

/-!
# Geometric restriction of sections, and naturality of `sectionsEquivSemiInvariants`

For closed subschemes `X' ⊆ X ⊆ Flₙ` (ideal sheaves `I ≤ I'`, closed immersion
`j : X' ⟶ X` with `j ≫ i = i'`):

* **`FlagVarieties.sectionsRestrict`**: the restriction `H⁰(X, i^* 𝓛(η)) → H⁰(X', i'^* 𝓛(η))`,
  pullback of sections along `j` followed by `j^* i^* ≅ (j ≫ i)^* = i'^*`;
* **`FlagVarieties.sectionsEquivSemiInvariants_sectionsRestrict`**: `sectionsEquivSemiInvariants` is
  natural: with `e = sectionsEquivSemiInvariants`,
  `e I' ∘ sectionsRestrict = (𝒪(GLₙ)/J ↠ 𝒪(GLₙ)/J') ∘ e I`;
* **`FlagVarieties.sectionsRestrictHom_eq_sectionsRestrict`**: `sectionsRestrictHom` (defined
  through `sectionsEquivSemiInvariants`) is the geometric restriction.

The key identity is `BorelAction.Hom.sectionFun_restrictSections`, for equivariant morphisms over
`X' ⟶ X ⟶ Y` in general: the function on `P'` of the restriction of a section is the pullback of
the function of the section. It is checked after adjunction, on pulled back sections, where both
sides are pullbacks of functions on the total space over `Y`.
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

/-! ### Restriction of sections of a pullback -/

section Units

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Pulling back a section along `g`, then along `f`, is pulling it back along `f ≫ g`. -/
theorem pullbackComp_unit (M : Z.Modules) (U : Z.Opens) (t : Γ(M, U)) :
    (((Scheme.Modules.pullbackComp f g).hom.app M).app (f ⁻¹ᵁ g ⁻¹ᵁ U)).hom
        ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          ((Scheme.Modules.pullback g).obj M)).app (g ⁻¹ᵁ U)).hom
        ((((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app U).hom t)) =
      (((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M).app U).hom t := by
  have h := unit_conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h
  have h2 := congrArg (fun φ => φ ≫ (Scheme.Modules.pushforward (f ≫ g)).map
    ((Scheme.Modules.pullbackComp f g).hom.app M)) h
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id] at h2
  have h3 := (congrArg (fun φ => (φ.app U).hom t) h2).symm
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforwardComp_hom_app_app, ConcreteCategory.comp_apply] at h3
  exact h3.symm

/-- Pulling back along equal morphisms. -/
theorem pullbackCongr_unit {f f' : X ⟶ Y} (hf : f = f') (M : Y.Modules) (U : Y.Opens)
    (t : Γ(M, U)) :
    (((Scheme.Modules.pullbackCongr hf).hom.app M).app (f ⁻¹ᵁ U)).hom
        ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U).hom t) =
      (((Scheme.Modules.pullback f').obj M).presheaf.map (eqToHom (by rw [hf])).op).hom
        ((((Scheme.Modules.pullbackPushforwardAdjunction f').unit.app M).app U).hom t) := by
  subst hf
  simp [Scheme.Modules.pullbackCongr]

variable {X' : Scheme.{u}}

theorem pullbackCongr_unit' {f : X' ⟶ X} {g : X ⟶ Y} {g' : X' ⟶ Y} (hfg : f ≫ g = g')
    (M : Y.Modules) (U : Y.Opens) (t : Γ(M, U)) :
    (((Scheme.Modules.pullbackCongr hfg).hom.app M).app (f ⁻¹ᵁ g ⁻¹ᵁ U)).hom
        ((((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M).app U).hom t) =
      (((Scheme.Modules.pullback g').obj M).presheaf.map (eqToHom (by rw [← hfg]; rfl)).op).hom
        ((((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app M).app U).hom t) :=
  pullbackCongr_unit hfg M U t

/-- **Restriction of global sections of a pullback**: for `f ≫ g = g'`, the map
`Γ(X, g^* N) → Γ(X', g'^* N)` (pull back along `f`, then `f^* g^* ≅ (f ≫ g)^* = g'^*`). -/
def restrictSections (f : X' ⟶ X) (g : X ⟶ Y) (g' : X' ⟶ Y) (hfg : f ≫ g = g') (N : Y.Modules)
    (s : Γ((Scheme.Modules.pullback g).obj N, ⊤)) : Γ((Scheme.Modules.pullback g').obj N, ⊤) :=
  (((Scheme.Modules.pullback g').obj N).presheaf.map
      (homOfLE (by simp) : (⊤ : X'.Opens) ⟶ f ⁻¹ᵁ ⊤).op).hom
    ((((Scheme.Modules.pullbackCongr hfg).hom.app N).app (f ⁻¹ᵁ ⊤)).hom
    ((((Scheme.Modules.pullbackComp f g).hom.app N).app (f ⁻¹ᵁ ⊤)).hom
      ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        ((Scheme.Modules.pullback g).obj N)).app ⊤).hom s)))

end Units

/-! ### Functions of sections under equivariant morphisms -/

namespace BorelAction

namespace Hom

variable {R : Type u} [CommRing R] {n : ℕ} {Y X X' : Scheme.{u}} {E₀ : BorelAction R n Y}
  {E : BorelAction R n X} {E' : BorelAction R n X'} {i : X ⟶ Y} {i' : X' ⟶ Y} {f : X' ⟶ X}

/-- `i^* 𝓛(η) ⟶ q_* 𝒪_P`: a section, as a function on the total space. -/
abbrev sectionFunMap (φ : Hom E E₀ i) (η : Fin n → ℤ) :
    (Scheme.Modules.pullback i).obj (E₀.semiInvariantSheaf η) ⟶ E.directImage :=
  φ.pullbackSemiInvariantSheafMap η ≫ E.semiInvariantι η

/-- On a pulled back section, the function is the pullback of the function on the total space
over `Y`. -/
theorem sectionFunMap_unit (φ : Hom E E₀ i) (η : Fin n → ℤ) (U : Y.Opens)
    (t : Γ(E₀.semiInvariantSheaf η, U)) :
    ((φ.sectionFunMap η).app (i ⁻¹ᵁ U)).hom
        ((((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          (E₀.semiInvariantSheaf η)).app U).hom t) =
      (φ.pullbackSections U).hom (((E₀.semiInvariantι η).app U).hom t) := by
  change ((E.semiInvariantι η).app (i ⁻¹ᵁ U)).hom
    (((φ.pullbackSemiInvariantSheafMap η).app (i ⁻¹ᵁ U)).hom
      ((((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (E₀.semiInvariantSheaf η)).app U).hom t)) = _
  rw [φ.pullbackSemiInvariantSheafMap_app_pullbackSection η U t]
  have h := congrArg (fun ψ => (ψ.app U).hom t) (φ.semiInvariantSheafMap_ι η)
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app] at h
  exact h

/-- **Restriction of sections, at the level of functions on total spaces.** -/
theorem sectionFunMap_restrict (φ : Hom E E₀ i) (φ' : Hom E' E₀ i') (ψ : Hom E' E f)
    (hf : f ≫ i = i') (hψ : ψ.j ≫ φ.j = φ'.j) (η : Fin n → ℤ) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        ((Scheme.Modules.pullback i).obj (E₀.semiInvariantSheaf η)) ≫
      (Scheme.Modules.pushforward f).map
        ((Scheme.Modules.pullbackComp f i).hom.app (E₀.semiInvariantSheaf η) ≫
          (Scheme.Modules.pullbackCongr hf).hom.app (E₀.semiInvariantSheaf η) ≫
            φ'.sectionFunMap η) =
      φ.sectionFunMap η ≫ ψ.directImageMap := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply Scheme.Modules.hom_ext
  intro U
  ext t
  change ((φ'.sectionFunMap η).app (f ⁻¹ᵁ i ⁻¹ᵁ U)).hom
      ((((Scheme.Modules.pullbackCongr hf).hom.app (E₀.semiInvariantSheaf η)).app
        (f ⁻¹ᵁ i ⁻¹ᵁ U)).hom
      ((((Scheme.Modules.pullbackComp f i).hom.app (E₀.semiInvariantSheaf η)).app
        (f ⁻¹ᵁ i ⁻¹ᵁ U)).hom
      ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        ((Scheme.Modules.pullback i).obj (E₀.semiInvariantSheaf η))).app (i ⁻¹ᵁ U)).hom
      ((((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (E₀.semiInvariantSheaf η)).app U).hom t)))) =
    (ψ.directImageMap.app (i ⁻¹ᵁ U)).hom (((φ.sectionFunMap η).app (i ⁻¹ᵁ U)).hom
      ((((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (E₀.semiInvariantSheaf η)).app U).hom t))
  rw [pullbackComp_unit, pullbackCongr_unit']
  have hnat := ConcreteCategory.congr_hom ((φ'.sectionFunMap η).mapPresheaf.naturality
    (eqToHom (by rw [← hf]; rfl) : f ⁻¹ᵁ i ⁻¹ᵁ U ⟶ i' ⁻¹ᵁ U).op)
    ((((Scheme.Modules.pullbackPushforwardAdjunction i').unit.app
      (E₀.semiInvariantSheaf η)).app U).hom t)
  change ((φ'.sectionFunMap η).app _).hom (((Scheme.Modules.pullback i').obj
    (E₀.semiInvariantSheaf η)).presheaf.map _ |>.hom _) =
      (E'.directImage.presheaf.map _).hom (((φ'.sectionFunMap η).app _).hom _) at hnat
  rw [hnat, sectionFunMap_unit, sectionFunMap_unit, directImageMap_app]
  change ((φ'.j.appLE _ _ (φ'.preimage_le U)) ≫ E'.P.presheaf.map _).hom _ =
    (ψ.j.appLE _ _ (ψ.preimage_le (i ⁻¹ᵁ U))).hom ((φ.j.appLE _ _ (φ.preimage_le U)).hom _)
  rw [Scheme.Hom.appLE_map]
  refine Eq.trans ?_ (appLE_comp_apply ψ.j φ.j _ _ (by
    rw [Scheme.Hom.comp_preimage]
    exact ψ.j.preimage_mono (φ.preimage_le U) |>.trans' (ψ.preimage_le _)) _)
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (appLE_eq_of_eq hψ.symm _ _)) _

/-- **The function of a restricted section is the pullback of the function of the section.** -/
theorem sectionFun_restrictSections (φ : Hom E E₀ i) (φ' : Hom E' E₀ i') (ψ : Hom E' E f)
    (hf : f ≫ i = i') (hψ : ψ.j ≫ φ.j = φ'.j) (η : Fin n → ℤ)
    (s : Γ((Scheme.Modules.pullback i).obj (E₀.semiInvariantSheaf η), ⊤)) :
    ((φ'.sectionFunMap η).app ⊤).hom (restrictSections f i i' hf _ s) =
      (ψ.j.appLE (E.q ⁻¹ᵁ ⊤) (E'.q ⁻¹ᵁ ⊤) (by simp)).hom (((φ.sectionFunMap η).app ⊤).hom s) := by
  have h : ((φ'.sectionFunMap η).app (f ⁻¹ᵁ ⊤)).hom
      ((((Scheme.Modules.pullbackCongr hf).hom.app (E₀.semiInvariantSheaf η)).app (f ⁻¹ᵁ ⊤)).hom
      ((((Scheme.Modules.pullbackComp f i).hom.app (E₀.semiInvariantSheaf η)).app (f ⁻¹ᵁ ⊤)).hom
      ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        ((Scheme.Modules.pullback i).obj (E₀.semiInvariantSheaf η))).app ⊤).hom s))) =
      (ψ.pullbackSections ⊤).hom (((φ.sectionFunMap η).app ⊤).hom s) :=
    congrArg (fun χ => (χ.app ⊤).hom s) (sectionFunMap_restrict φ φ' ψ hf hψ η)
  have hnat := ConcreteCategory.congr_hom ((φ'.sectionFunMap η).mapPresheaf.naturality
    (homOfLE (by simp) : (⊤ : X'.Opens) ⟶ f ⁻¹ᵁ ⊤).op)
    ((((Scheme.Modules.pullbackCongr hf).hom.app (E₀.semiInvariantSheaf η)).app (f ⁻¹ᵁ ⊤)).hom
    ((((Scheme.Modules.pullbackComp f i).hom.app (E₀.semiInvariantSheaf η)).app (f ⁻¹ᵁ ⊤)).hom
      ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        ((Scheme.Modules.pullback i).obj (E₀.semiInvariantSheaf η))).app ⊤).hom s)))
  change ((φ'.sectionFunMap η).app ⊤).hom (restrictSections f i i' hf _ s) =
    (E'.directImage.presheaf.map _).hom (((φ'.sectionFunMap η).app _).hom _) at hnat
  rw [hnat, h]
  change ((ψ.j.appLE _ _ (ψ.preimage_le ⊤)) ≫ E'.P.presheaf.map _).hom _ = _
  rw [Scheme.Hom.appLE_map]

end Hom

end BorelAction

/-! ### The inclusion `π⁻¹(X') ⟶ π⁻¹(X)` -/

section Inclusion

variable (R : Type u) [CommRing R] (n : ℕ) {I I' : (FlagScheme R n).IdealSheafData} (h : I ≤ I')

/-- `π⁻¹(X') ⟶ π⁻¹(X)` for `X' ⊆ X`. -/
def preimageInclusion' : preimageScheme R n I' ⟶ preimageScheme R n I :=
  pullback.lift (preimageι R n I') (preimageProj R n I' ≫ Scheme.IdealSheafData.inclusion h) (by
    rw [Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
    exact pullback.condition)

@[reassoc (attr := simp)] theorem preimageInclusion'_ι :
    preimageInclusion' R n h ≫ preimageι R n I = preimageι R n I' :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem preimageInclusion'_proj :
    preimageInclusion' R n h ≫ preimageProj R n I =
      preimageProj R n I' ≫ Scheme.IdealSheafData.inclusion h :=
  pullback.lift_snd _ _ _

theorem preimageInclusion'_toSpec :
    preimageInclusion' R n h ≫ preimageToSpec R n I = preimageToSpec R n I' := by
  rw [preimageToSpec, preimageInclusion'_ι_assoc]

theorem preimageInclusion'_prodMap :
    pullback.map _ _ _ _ (preimageInclusion' R n h) (𝟙 _) (𝟙 _)
        ((Category.comp_id _).trans (preimageInclusion'_toSpec R n h).symm)
        (by simp) ≫ preimageProdMap R n I = preimageProdMap R n I' := by
  apply pullback.hom_ext <;> simp [preimageProdMap]

theorem preimageInclusion'_act :
    preimageAct R n I' ≫ preimageInclusion' R n h =
      pullback.map _ _ _ _ (preimageInclusion' R n h) (𝟙 _) (𝟙 _)
        ((Category.comp_id _).trans (preimageInclusion'_toSpec R n h).symm)
        (by simp) ≫ preimageAct R n I := by
  apply pullback.hom_ext
  · rw [Category.assoc, preimageInclusion'_ι, preimageAct, pullback.lift_fst, Category.assoc,
      preimageAct, pullback.lift_fst, ← Category.assoc (pullback.map _ _ _ _ _ _ _ _ _),
      preimageInclusion'_prodMap]
  · simp [preimageAct, preimageInclusion'_proj]

/-- `π⁻¹(X') ⟶ π⁻¹(X)` is `B`-equivariant over `X' ⟶ X`. -/
def preimageInclusionHom :
    BorelAction.Hom (preimageAction R n I') (preimageAction R n I)
      (Scheme.IdealSheafData.inclusion h) where
  j := preimageInclusion' R n h
  j_q := preimageInclusion'_proj R n h
  j_toSpec := preimageInclusion'_toSpec R n h
  act_j := preimageInclusion'_act R n h

end Inclusion

/-! ### Geometric restriction of sections -/

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The underlying map of `sectionsRestrict`. -/
def sectionsRestrictAux {I I' : (FlagScheme R n).IdealSheafData} (h : I ≤ I')
    (η : Fin n → ℤ) (s : sections R n I η) : sections R n I' η :=
  restrictSections (Scheme.IdealSheafData.inclusion h) I.subschemeι I'.subschemeι
    (Scheme.IdealSheafData.inclusion_subschemeι h) (lineBundle R n η) s

variable {R n} {I I' : (FlagScheme R n).IdealSheafData} (h : I ≤ I') (η : Fin n → ℤ)

/-- The function on `π⁻¹(X')` of the restriction of a section. -/
theorem sectionX_sectionsRestrictAux (s : sections R n I η) :
    sectionX R n I' η (((lineBundleComparison R n I' η).app ⊤).hom
        (sectionsRestrictAux R n h η s)) =
      ((preimageInclusion' R n h).appLE (preimageProj R n I ⁻¹ᵁ ⊤) (preimageProj R n I' ⁻¹ᵁ ⊤)
        (by simp)).hom (sectionX R n I η (((lineBundleComparison R n I η).app ⊤).hom s)) :=
  BorelAction.Hom.sectionFun_restrictSections (preimageHom R n I) (preimageHom R n I')
    (preimageInclusionHom R n h) (Scheme.IdealSheafData.inclusion_subschemeι h)
    (preimageInclusion'_ι R n h) η s

theorem preimageQuotEquiv_factor (x : GLCoord R n ⧸ preimageIdeal R n I) :
    preimageQuotEquiv R n I' (Ideal.Quotient.factorₐ R (preimageIdeal_mono R n h) x) =
      ((preimageInclusion' R n h).appLE (preimageProj R n I ⁻¹ᵁ ⊤) (preimageProj R n I' ⁻¹ᵁ ⊤)
        (by simp)).hom (preimageQuotEquiv R n I x) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  change preimageRestrictSections R n I' f = _
  rw [preimageQuotEquiv_mk, preimageRestrictSections, preimageRestrictSections, RingHom.comp_apply,
    RingHom.comp_apply, ← appLE_top_top (preimageι R n I) (by simp),
    ← appLE_top_top (preimageι R n I') (by simp)]
  refine Eq.trans ?_ (appLE_comp_apply (preimageInclusion' R n h) (preimageι R n I) _ _
    (by simp) _)
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (appLE_eq_of_eq (preimageInclusion'_ι R n h).symm _ _)) _

/-- **`sectionsEquivSemiInvariants` is natural** (function level). -/
theorem sectionsEquivSemiInvariants_sectionsRestrictAux (s : sections R n I η) :
    sectionsEquivSemiInvariants R n I' η (sectionsRestrictAux R n h η s) =
      semiInvariantsRestrict (preimageIdeal_mono R n h) η
          (sectionsEquivSemiInvariants R n I η s) := by
  apply Subtype.ext
  apply (preimageQuotEquiv R n I').injective
  rw [preimageQuotEquiv_sectionsEquivSemiInvariants, coe_semiInvariantsRestrict,
      preimageQuotEquiv_factor,
    preimageQuotEquiv_sectionsEquivSemiInvariants]
  exact sectionX_sectionsRestrictAux h η s

theorem sectionsRestrictAux_eq (s : sections R n I η) :
    sectionsRestrictAux R n h η s = (sectionsEquivSemiInvariants R n I' η).symm
      (semiInvariantsRestrict (preimageIdeal_mono R n h) η
          (sectionsEquivSemiInvariants R n I η s)) := by
  rw [← sectionsEquivSemiInvariants_sectionsRestrictAux, LinearEquiv.symm_apply_apply]

variable (R n)

/-- **The restriction of sections** `H⁰(X, 𝓛(η)) → H⁰(X', 𝓛(η))` for closed subschemes
`X' ⊆ X` (ideal sheaves `I ≤ I'`): pull back a section of
`i^* 𝓛(η)` along the closed immersion `j : X' ⟶ X`, then identify `j^* i^* 𝓛(η)` with
`(j ≫ i)^* 𝓛(η) = i'^* 𝓛(η)` (`restrictSections`). -/
def sectionsRestrict : sections R n I η →ₗ[R] sections R n I' η :=
  ((sectionsEquivSemiInvariants R n I' η).symm.toLinearMap ∘ₗ
      semiInvariantsRestrict (preimageIdeal_mono R n h) η ∘ₗ
        (sectionsEquivSemiInvariants R n I η).toLinearMap).copy (sectionsRestrictAux R n h η)
    (funext fun s => sectionsRestrictAux_eq h η s)

variable {R n}

/-- **`sectionsEquivSemiInvariants` is natural for `X' ⊆ X`**: restricting a section corresponds to
the quotient
map `𝒪(GLₙ)/J → 𝒪(GLₙ)/J'` on semi-invariants. -/
theorem sectionsEquivSemiInvariants_sectionsRestrict (s : sections R n I η) :
    sectionsEquivSemiInvariants R n I' η (sectionsRestrict R n h η s) =
      semiInvariantsRestrict (preimageIdeal_mono R n h) η (sectionsEquivSemiInvariants R n I η s) :=
  sectionsEquivSemiInvariants_sectionsRestrictAux h η s

/-- **`sectionsRestrictHom` is the geometric restriction of sections** (every `R`). -/
theorem sectionsRestrictHom_eq_sectionsRestrict
    (hJ : IsLeftTranslStable (preimageIdeal R n I))
    (hJ' : IsLeftTranslStable (preimageIdeal R n I')) :
    (sectionsRestrictHom R n h η hJ hJ').toLinearMap = sectionsRestrict R n h η :=
  LinearMap.ext fun s => (sectionsEquivSemiInvariants R n I' η).injective <| by
    change sectionsEquivSemiInvariants R n I' η (sectionsRestrictHom R n h η hJ hJ' s) = _
    rw [sectionsEquivSemiInvariants_sectionsRestrictHom,
        sectionsEquivSemiInvariants_sectionsRestrict]

end FlagVarieties
