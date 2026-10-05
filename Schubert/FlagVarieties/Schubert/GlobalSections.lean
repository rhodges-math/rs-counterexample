import Schubert.FlagVarieties.Schubert.Orbit
import Schubert.FlagVarieties.LineBundle.SectionsAsSemiInvariants
import Schubert.FlagVarieties.LineBundle.Density
import Schubert.FlagVarieties.Flag.Proper

/-!
# Constant global sections `Γ(X_w, 𝒪) = K`

* `FlagVarieties.isIntegral_schubertVariety`: over a field, `X_w` is integral (the image of the
  integral scheme `B`).
* `FlagVarieties.schubertVariety_globalSections_const`: **every global function on `X_w` is
  constant**: `X_w` is integral, proper over `K` and has the `K`-point `ẇE•`.
* `FlagVarieties.exists_eq_preimageProj_of_isSemiInvariant`: for a closed subscheme `X ⊆ Flₙ`,
  every `B`-invariant function on `π⁻¹(X)` is pulled back from `X` (`𝒪_X ≅ 𝓛_X(0)`).
* `FlagVarieties.exists_sub_algebraMap_mem_schubertOrbitIdeal`: **the ring form of
  `Γ(X_w, 𝒪) = K`**: a function on `GLₙ` whose restriction to `π⁻¹(X_w)` is invariant under right
  translation by `B` is constant modulo the orbit ideal of `w`.
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

/-! ### Invariant functions on `π⁻¹(X)` descend to `X` -/

section Descent

variable (R : Type u) [CommRing R] (n : ℕ) (I : (FlagScheme R n).IdealSheafData)

theorem exists_lineBundleXOne : ∃ s : Γ(lineBundleX R n I 0, ⊤), sectionX R n I 0 s = 1 :=
  ((preimageAction R n I).mem_range_semiInvariantι_app_iff 0 ⊤
    (show Γ((preimageAction R n I).directImage, ⊤) from
      (1 : Γ((preimageAction R n I).P, (preimageAction R n I).q ⁻¹ᵁ ⊤)))).mpr
    (BorelAction.IsSemiInvariant.one (preimageAction R n I) ⊤)

/-- The global section `1` of `𝓛_X(0)`. -/
def lineBundleXOne : Γ(lineBundleX R n I 0, ⊤) :=
  (exists_lineBundleXOne R n I).choose

theorem sectionX_lineBundleXOne : sectionX R n I 0 (lineBundleXOne R n I) = 1 :=
  (exists_lineBundleXOne R n I).choose_spec

theorem bigCellTwistUnit_zero (v : Equiv.Perm (Fin n)) : bigCellTwistUnit R v 0 = 1 := by
  simp [bigCellTwistUnit]

/-- Over `X ∩ bigCell v`, the basis section of `𝓛_X(0)` is the restriction of `1`. -/
theorem lineBundleXSection_zero (v : Equiv.Perm (Fin n)) :
    lineBundleXSection R n I 0 v = ((lineBundleX R n I 0).presheaf.map
      (homOfLE le_top : bigCellX R n I v ⟶ ⊤).op).hom (lineBundleXOne R n I) := by
  have hinj : Function.Injective
      (((preimageAction R n I).semiInvariantι 0).app (bigCellX R n I v)).hom :=
    kernel_ι_app_injective
      ((preimageAction R n I).pullbackAct - (preimageAction R n I).pullbackTwist 0)
      (bigCellX R n I v)
  apply hinj
  refine (lineBundleXSection_ι R n I 0 v).trans ?_
  rw [bigCellTwistUnit_zero, Units.val_one]
  refine (map_one ((preimageHom R n I).pullbackSections (bigCell R v)).hom).trans ?_
  have h := ConcreteCategory.congr_hom
    (((preimageAction R n I).semiInvariantι 0).mapPresheaf.naturality
      (homOfLE le_top : bigCellX R n I v ⟶ ⊤).op) (lineBundleXOne R n I)
  refine Eq.trans ?_ h.symm
  change (1 : Γ((preimageAction R n I).P, (preimageAction R n I).q ⁻¹ᵁ bigCellX R n I v)) =
    ((preimageAction R n I).P.presheaf.map _).hom (sectionX R n I 0 (lineBundleXOne R n I))
  rw [sectionX_lineBundleXOne]
  exact (map_one _).symm

/-- **`𝒪_X ≅ 𝓛_X(0)`**, `1 ↦ 1`. -/
theorem isIso_unitHomOfSection_lineBundleXOne :
    IsIso (unitHomOfSection (lineBundleX R n I 0) (lineBundleXOne R n I)) := by
  refine isIso_of_forall_bijective _ (ι := ULift.{u} (Equiv.Perm (Fin n)))
    (fun v => bigCellX R n I v.down) ?_ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨v, hv⟩ := exists_mem_bigCell R (I.subschemeι x)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨v⟩, hv⟩
  · rintro ⟨v⟩ W hW
    have e : ⇑((unitHomOfSection (lineBundleX R n I 0) (lineBundleXOne R n I)).app W).hom =
        fun a : Γ(I.subscheme, W) => a • ((lineBundleX R n I 0).presheaf.map
          (homOfLE hW).op).hom (lineBundleXSection R n I 0 v) := by
      funext a
      refine (unitHomOfSection_app _ _ W a).trans ?_
      congr 1
      rw [lineBundleXSection_zero, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    change Function.Bijective
      ⇑((unitHomOfSection (lineBundleX R n I 0) (lineBundleXOne R n I)).app W).hom
    rw [e]
    exact bijective_smul_lineBundleXSection R n I 0 v hW

/-- **Invariant functions on `π⁻¹(X)` descend to `X`.** -/
theorem exists_eq_preimageProj_of_isSemiInvariant (f : Γ(preimageScheme R n I, ⊤))
    (hf : (preimageAction R n I).IsSemiInvariant 0 (W := ⊤) f) :
    ∃ a : Γ(I.subscheme, ⊤), f = (preimageProj R n I).appTop a := by
  obtain ⟨x, hx⟩ := ((preimageAction R n I).mem_range_semiInvariantι_app_iff 0 ⊤ f).mpr hf
  have := isIso_unitHomOfSection_lineBundleXOne R n I
  obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso
    ((unitHomOfSection (lineBundleX R n I 0) (lineBundleXOne R n I)).app ⊤)).2 x
  let a' : Γ(I.subscheme, ⊤) := a
  refine ⟨a', ?_⟩
  have ha' : a' • ((lineBundleX R n I 0).presheaf.map
      (homOfLE le_top : (⊤ : I.subscheme.Opens) ⟶ ⊤).op).hom (lineBundleXOne R n I) = x :=
    (unitHomOfSection_app _ _ ⊤ a').symm.trans ha
  have hid : ((lineBundleX R n I 0).presheaf.map
      (homOfLE le_top : (⊤ : I.subscheme.Opens) ⟶ ⊤).op).hom (lineBundleXOne R n I) =
      lineBundleXOne R n I := by
    rw [show (homOfLE le_top : (⊤ : I.subscheme.Opens) ⟶ ⊤) = 𝟙 _ from rfl, op_id,
      CategoryTheory.Functor.map_id]
    rfl
  rw [hid] at ha'
  have h := congrArg (sectionX R n I 0) ha'
  rw [sectionX_smul, sectionX_lineBundleXOne, mul_one] at h
  exact hx.symm.trans h.symm

/-- If the global functions on `X` are constant, then every function on `GLₙ` whose restriction
to `π⁻¹(X)` is `B`-invariant is constant on `π⁻¹(X)`. -/
theorem exists_sub_mem_preimageIdeal
    (hconst : ∀ a : Γ(I.subscheme, ⊤),
      ∃ r : R, a = Scheme.Modules.baseRingToGlobalSections R I.subscheme r)
    (f : GLCoord R n) (hf : semiInvariantDefect R n (preimageIdeal R n I) 0 f = 0) :
    ∃ r : R, f - algebraMap R (GLCoord R n) r ∈ preimageIdeal R n I := by
  have hs := (isSemiInvariant_preimageRestrictSections_iff R n I 0 f).mpr hf
  obtain ⟨a, ha⟩ := exists_eq_preimageProj_of_isSemiInvariant R n I _ hs
  obtain ⟨r, rfl⟩ := hconst a
  refine ⟨r, ?_⟩
  rw [← ker_preimageRestrictSections, RingHom.mem_ker, map_sub, ha, preimageProj_baseRing, sub_self]

end Descent

/-! ### Global functions on `X_w` -/

section Geometry

variable (K : Type u) [Field K] (n : ℕ) (w : Equiv.Perm (Fin n))

/-- **`X_w` is integral** (over a field): it is the scheme-theoretic image of the integral
scheme `B`. -/
theorem isIntegral_schubertVariety : IsIntegral (schubertVariety K n w).subscheme := by
  have := isAffineHom_schubertOrbitMap K n w
  have : IsAffineHom ((schubertOrbitMap K n w).toImage ≫ (schubertOrbitMap K n w).imageι) := by
    rw [Scheme.Hom.toImage_imageι]
    infer_instance
  have : IsAffineHom (schubertOrbitMap K n w).toImage :=
    IsAffineHom.of_comp _ (schubertOrbitMap K n w).imageι
  have : IsSchemeTheoreticallyDominant (schubertOrbitMap K n w).toImage :=
    isSchemeTheoreticallyDominant_toImage _
  have hred : IsReduced (schubertOrbitMap K n w).image :=
    IsSchemeTheoreticallyDominant.isReduced (schubertOrbitMap K n w).toImage
  have : IsReduced (schubertVariety K n w).subscheme := hred
  have : Nonempty (schubertVariety K n w).subscheme :=
    ⟨(schubertOrbitMap K n w).toImage (Nonempty.some inferInstance)⟩
  have : IrreducibleSpace (schubertVariety K n w).subscheme := by
    refine (irreducibleSpace_def _).mpr ?_
    have hirr : IsIrreducible (Set.range (schubertOrbitMap K n w).toImage) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).image _
        (schubertOrbitMap K n w).toImage.continuous.continuousOn
    have h := hirr.closure
    rw [(schubertOrbitMap K n w).toImage.denseRange.closure_range] at h
    exact h
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The `K`-point `ẇE•` of `X_w`, the image of `1 ∈ B`. -/
def schubertBasePoint : Spec (CommRingCat.of K) ⟶ (schubertVariety K n w).subscheme :=
  Spec.map (CommRingCat.ofHom (borelCounit K n).toRingHom) ≫ (schubertOrbitMap K n w).toImage

theorem schubertBasePoint_toSpec :
    schubertBasePoint K n w ≫ (schubertVariety K n w).subschemeι ≫ FlagScheme.toSpec K n =
      𝟙 _ := by
  change Spec.map _ ≫ (schubertOrbitMap K n w).toImage ≫ (schubertOrbitMap K n w).imageι ≫ _ = _
  rw [Scheme.Hom.toImage_imageι_assoc, schubertOrbitMap_toSpec, BorelScheme.toSpec,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [show (borelCounit K n).toRingHom.comp (algebraMap K (BorelCoord K n)) = RingHom.id K from
    RingHom.ext fun r => (borelCounit K n).commutes r]
  rw [CommRingCat.ofHom_id, Spec.map_id]

/-- **`Γ(X_w, 𝒪) = K`**: every global function on the Schubert variety `X_w` is constant. -/
theorem schubertVariety_globalSections_const (a : Γ((schubertVariety K n w).subscheme, ⊤)) :
    ∃ c : K, a = Scheme.Modules.baseRingToGlobalSections K (schubertVariety K n w).subscheme c := by
  have := isIntegral_schubertVariety K n w
  have : UniversallyClosed ((schubertVariety K n w).subschemeι ≫ FlagScheme.toSpec K n) :=
    inferInstance
  have hsf (b : Γ(Spec (CommRingCat.of K), ⊤)) : (schubertBasePoint K n w).appTop
      (((schubertVariety K n w).subschemeι ≫ FlagScheme.toSpec K n).appTop b) = b := by
    have h := ConcreteCategory.congr_hom
      (congrArg (fun g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) => g.appTop)
        (schubertBasePoint_toSpec K n w)) b
    simp only [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop, CommRingCat.comp_apply,
      CommRingCat.id_apply] at h ⊢
    exact h
  let := (isField_of_universallyClosed K
    ((schubertVariety K n w).subschemeι ≫ FlagScheme.toSpec K n)).toField
  have hinj : Function.Injective (schubertBasePoint K n w).appTop :=
    (schubertBasePoint K n w).appTop.hom.injective
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom ((schubertBasePoint K n w).appTop a), ?_⟩
  have e : (Scheme.ΓSpecIso (CommRingCat.of K)).inv ((Scheme.ΓSpecIso (CommRingCat.of K)).hom
      ((schubertBasePoint K n w).appTop a)) = (schubertBasePoint K n w).appTop a := by
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
  refine (hinj (hsf ((schubertBasePoint K n w).appTop a))).symm.trans ?_
  change _ = ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
    ((schubertVariety K n w).subschemeι ≫ FlagScheme.toSpec K n).appTop).hom
      ((Scheme.ΓSpecIso (CommRingCat.of K)).hom ((schubertBasePoint K n w).appTop a))
  rw [CommRingCat.comp_apply, e]

end Geometry

/-! ### The ring form of `Γ(X_w, 𝒪) = K` -/

/-- **The ring form of `Γ(X_w, 𝒪) = K`** (over a field): a function on `GLₙ` whose restriction to
`π⁻¹(X_w)` (the closure of `B ẇ B`) is invariant under right translation by `B` is constant
modulo the orbit ideal of `w`. -/
theorem exists_sub_algebraMap_mem_schubertOrbitIdeal (K : Type u) [Field K] (n : ℕ)
    (w : Equiv.Perm (Fin n))
    (f : GLCoord K n) (hf : semiInvariantDefect K n (schubertOrbitIdeal K n w) 0 f = 0) :
    ∃ c : K, f - algebraMap K (GLCoord K n) c ∈ schubertOrbitIdeal K n w := by
  rw [← preimageIdeal_schubertVariety_eq_schubertOrbitIdeal K n w] at hf ⊢
  exact exists_sub_mem_preimageIdeal K n _ (schubertVariety_globalSections_const K n w) f hf

end FlagVarieties
