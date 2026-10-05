import Schubert.FlagVarieties.Schubert.Orbit

/-!
# Preimages in `GLₙ` and the lattice of closed subschemes of `Flₙ`

* `FlagVarieties.comap_ker_eq_ker_fst`: for flat `π` and quasi-compact `h`, the pullback along `π`
  of the scheme-theoretic image of `h` is the scheme-theoretic image of `pullback.fst π h`.
* `FlagVarieties.comap_inf_of_flat`: pulling back ideal sheaves along a flat morphism commutes
  with `⊓` (scheme-theoretic unions of closed subschemes).
* `FlagVarieties.preimageIdeal_le_preimageIdeal_iff`: the preimage under `π : GLₙ ⟶ Flₙ` reflects
  inclusions (for every `R`; `π` has sections over the big cells).
* `FlagVarieties.preimageIdeal_finsetInf`: `π⁻¹` commutes with finite infima of ideal sheaves
  (when `𝒪(B)` is flat over `R`).
* `FlagVarieties.preimageIdeal_schubertUnion`: the ideal of `π⁻¹(X_S)` is `⋂_{w ∈ S}` of the orbit
  ideals of `w`.
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-! ### Flat base change and unions -/

/-- **Images commute with flat base change**: for flat `π` and quasi-compact `h`, the pullback
along `π` of the scheme-theoretic image of `h` is the scheme-theoretic image of the base change
`pullback.fst π h` of `h`. -/
theorem comap_ker_eq_ker_fst {X Y Z : Scheme.{u}} (π : Z ⟶ Y) (h : X ⟶ Y) [Flat π]
    [QuasiCompact h] : h.ker.comap π = (pullback.fst π h).ker := by
  rw [comap_ker_eq_ker]
  have key : ∀ (h' : X ⟶ Y) (_ : h.toImage ≫ h.imageι = h'),
      (pullback.fst (pullback.snd π h.imageι) h.toImage ≫ pullback.fst π h.imageι).ker =
        (pullback.fst π h').ker := by
    rintro _ rfl
    rw [← pullbackLeftPullbackSndIso_hom_fst π h.imageι h.toImage, Scheme.Hom.ker_comp_of_isIso]
  exact key h (Scheme.Hom.toImage_imageι h)

/-- The union of two closed subschemes is the image of their disjoint union. -/
theorem ker_coprodDesc_subschemeι {Y : Scheme.{u}} (I J : Y.IdealSheafData) :
    (coprod.desc I.subschemeι J.subschemeι).ker = I ⊓ J := by
  apply le_antisymm
  · refine le_inf ?_ ?_
    · have := (coprod.inl : I.subscheme ⟶ _).le_ker_comp (coprod.desc I.subschemeι J.subschemeι)
      rwa [coprod.inl_desc, Scheme.IdealSheafData.ker_subschemeι] at this
    · have := (coprod.inr : J.subscheme ⟶ _).le_ker_comp (coprod.desc I.subschemeι J.subschemeι)
      rwa [coprod.inr_desc, Scheme.IdealSheafData.ker_subschemeι] at this
  · rw [← Scheme.Hom.iInf_ker_openCover_map_comp _ (coprodOpenCover.{u, 0} I.subscheme J.subscheme)]
    refine le_iInf fun i => ?_
    rcases i with ⟨⟩ | ⟨⟩
    · change I ⊓ J ≤ (coprod.inl ≫ coprod.desc I.subschemeι J.subschemeι).ker
      rw [coprod.inl_desc, Scheme.IdealSheafData.ker_subschemeι]
      exact inf_le_left
    · change I ⊓ J ≤ (coprod.inr ≫ coprod.desc I.subschemeι J.subschemeι).ker
      rw [coprod.inr_desc, Scheme.IdealSheafData.ker_subschemeι]
      exact inf_le_right

/-- **Pulling back along a flat morphism commutes with unions of closed subschemes.** -/
theorem comap_inf_of_flat {Y Z : Scheme.{u}} (π : Z ⟶ Y) [Flat π] (I J : Y.IdealSheafData) :
    (I ⊓ J).comap π = I.comap π ⊓ J.comap π := by
  apply le_antisymm
  · exact le_inf (Scheme.IdealSheafData.comap_mono π inf_le_left)
      (Scheme.IdealSheafData.comap_mono π inf_le_right)
  let h := coprod.desc I.subschemeι J.subschemeι
  rw [← ker_coprodDesc_subschemeι I J, comap_ker_eq_ker_fst π h,
    ← Scheme.Hom.iInf_ker_openCover_map_comp _
      ((coprodOpenCover.{u, 0} I.subscheme J.subscheme).pullback₁ (pullback.snd π h))]
  refine le_iInf fun i => ?_
  rcases i with ⟨⟩ | ⟨⟩
  · let p := pullback.fst (pullback.snd π h) (coprod.inl : I.subscheme ⟶ _)
    have hc : (p ≫ pullback.fst π h) ≫ π =
        pullback.snd (pullback.snd π h) (coprod.inl : I.subscheme ⟶ _) ≫ I.subschemeι := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
        Category.assoc, coprod.inl_desc]
    change _ ≤ (p ≫ pullback.fst π h).ker
    rw [← pullback.lift_fst _ _ hc]
    exact inf_le_left.trans (Scheme.Hom.le_ker_comp _ _)
  · let p := pullback.fst (pullback.snd π h) (coprod.inr : J.subscheme ⟶ _)
    have hc : (p ≫ pullback.fst π h) ≫ π =
        pullback.snd (pullback.snd π h) (coprod.inr : J.subscheme ⟶ _) ≫ J.subschemeι := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
        Category.assoc, coprod.inr_desc]
    change _ ≤ (p ≫ pullback.fst π h).ker
    rw [← pullback.lift_fst _ _ hc]
    exact inf_le_right.trans (Scheme.Hom.le_ker_comp _ _)

/-! ### Preimages in `GLₙ` -/

variable (R : Type u) [CommRing R] (n : ℕ)

theorem glCoordToGlobal_surjective : Function.Surjective (glCoordToGlobal R n) := by
  have : IsIso ((TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom.app ⊤) := inferInstance
  exact (ConcreteCategory.bijective_of_isIso
    ((Scheme.ΓSpecIso (CommRingCat.of (GLCoord R n))).inv ≫
      (TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom.app ⊤)).2

theorem preimageIdeal_mono {I J : (FlagScheme R n).IdealSheafData} (h : I ≤ J) :
    preimageIdeal R n I ≤ preimageIdeal R n J :=
  Ideal.comap_mono (Scheme.IdealSheafData.comap_mono (FlagScheme.orbitMap R n) h _)

/-- **The preimage under `π : GLₙ ⟶ Flₙ` reflects inclusions** (for every `R`): `π` has a section
over every big cell, and the big cells cover `Flₙ`. -/
theorem preimageIdeal_le_preimageIdeal_iff (I J : (FlagScheme R n).IdealSheafData) :
    preimageIdeal R n I ≤ preimageIdeal R n J ↔ I ≤ J := by
  refine ⟨fun h => ?_, preimageIdeal_mono R n⟩
  have := isAffine_glScheme R n
  have h1 : (I.comap (FlagScheme.orbitMap R n)).ideal ⟨⊤, isAffineOpen_top _⟩ ≤
      (J.comap (FlagScheme.orbitMap R n)).ideal ⟨⊤, isAffineOpen_top _⟩ :=
    (Ideal.comap_le_comap_iff_of_surjective _ (glCoordToGlobal_surjective R n) _ _).mp h
  have h2 := Scheme.IdealSheafData.le_of_isAffine h1
  have : ∀ v : Equiv.Perm (Fin n), IsAffine (bigCellChartScheme R v) := fun v =>
    inferInstanceAs (IsAffine (Spec _))
  refine Scheme.IdealSheafData.le_of_iSup_eq_top (fun v : Equiv.Perm (Fin n) =>
    ⟨bigCellChart R v ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion _⟩) ?_ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨v, hv⟩ := exists_mem_bigCell R x
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨v, ?_⟩
    change x ∈ bigCellChart R v ''ᵁ ⊤
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact hv
  · intro v
    have h3 := Scheme.IdealSheafData.comap_mono (bigCellSection R v) h2
    simp only [← Scheme.IdealSheafData.comap_comp, bigCellSection_orbitMap] at h3
    have h4 := h3 ⟨⊤, isAffineOpen_top _⟩
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
      Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at h4
    exact (Ideal.comap_le_comap_iff_of_surjective _
      (ConcreteCategory.bijective_of_isIso ((bigCellChart R v).appIso ⊤).inv).2 _ _).mp h4

theorem preimageIdeal_injective : Function.Injective (preimageIdeal R n) := fun I J h =>
  le_antisymm ((preimageIdeal_le_preimageIdeal_iff R n I J).mp h.le)
    ((preimageIdeal_le_preimageIdeal_iff R n J I).mp h.ge)

/-- **The preimage reflects inclusions, over a field.** -/
theorem le_of_preimageIdeal_le (K : Type u) [Field K] (n : ℕ) :
    ∀ I J : (FlagScheme K n).IdealSheafData, preimageIdeal K n I ≤ preimageIdeal K n J → I ≤ J :=
  fun I J => (preimageIdeal_le_preimageIdeal_iff K n I J).mp

theorem preimageIdeal_top : preimageIdeal R n ⊤ = ⊤ := by
  rw [preimageIdeal, Scheme.IdealSheafData.comap_top, Scheme.IdealSheafData.ideal_top]
  exact Ideal.comap_top

/-- **`π⁻¹(X ∪ Y) = π⁻¹(X) ∪ π⁻¹(Y)`** (when `𝒪(B)` is flat over `R`). -/
theorem preimageIdeal_inf [Module.Flat R (BorelCoord R n)] (I J : (FlagScheme R n).IdealSheafData) :
    preimageIdeal R n (I ⊓ J) = preimageIdeal R n I ⊓ preimageIdeal R n J := by
  rw [preimageIdeal, comap_inf_of_flat, Scheme.IdealSheafData.ideal_inf]
  exact Ideal.comap_inf _ _ _

/-- **`π⁻¹` commutes with finite unions of closed subschemes** (when `𝒪(B)` is flat over `R`). -/
theorem preimageIdeal_finsetInf [Module.Flat R (BorelCoord R n)] {ι : Type*} (S : Finset ι)
    (I : ι → (FlagScheme R n).IdealSheafData) :
    preimageIdeal R n (⨅ i ∈ S, I i) = ⨅ i ∈ S, preimageIdeal R n (I i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using preimageIdeal_top R n
  | insert a S _ ih => rw [Finset.iInf_insert, Finset.iInf_insert, preimageIdeal_inf, ih]

/-- **The ideal of `π⁻¹(X_S)` is the intersection of the orbit ideals** (when `𝒪(B)` is flat over
`R`, e.g. over a field). -/
theorem preimageIdeal_schubertUnion [Module.Flat R (BorelCoord R n)]
    (S : Finset (Equiv.Perm (Fin n))) :
    preimageIdeal R n (schubertUnion R n S) = ⨅ w ∈ S, schubertOrbitIdeal R n w := by
  rw [schubertUnion, preimageIdeal_finsetInf]
  simp only [preimageIdeal_schubertVariety]

end FlagVarieties
