import RSCounterexample.FlagVarieties.Bruhat.Dimension.Scheme
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Scheme-theoretic images and pullbacks of ideal sheaves on affine schemes

* `isIntegral_image`: the scheme-theoretic image of a quasi-compact morphism from an integral
  scheme is integral (reduced: its coordinate rings on affine opens embed into those of the
  source; irreducible: it is the closure of the image).
* `specIdeal I`: the ideal of `A` of an ideal sheaf `I` on `Spec A`; `specIdeal_ker_spec_map`:
  `Spec (A/a) ⟶ Spec A` has ideal `a`.
* `specIdeal_comap_spec_map`: **pulling back along `Spec B ⟶ Spec A` extends the ideal**,
  `specIdeal (I.comap (Spec.map φ)) = (specIdeal I).map φ` (through `Spec (B ⊗_A A/a)`).
* `comap_eq_map_inv`, `ideal_top_comap_of_isIso`: pulling back along an isomorphism.
-/

namespace FlagVarieties.Dimension

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-! ### Integrality of scheme-theoretic images -/

section Image

variable {Z Y : Scheme.{u}} (f : Z ⟶ Y) [QuasiCompact f]

theorem isReduced_image [IsReduced Z] : IsReduced f.image := by
  have h : ∀ U : Y.affineOpens, IsReduced (f.ker.subschemeCover.openCover.X U) := by
    intro U
    have hinj := f.toImage_app_injective U
    have : _root_.IsReduced (Γ(Y, U) ⧸ f.ker.ideal U) :=
      isReduced_of_injective ((f.toImage.app (f.imageι ⁻¹ᵁ U)).hom.comp
        (f.ker.subschemeObjIso U).inv.hom)
        (hinj.comp (ConcreteCategory.bijective_of_isIso (f.ker.subschemeObjIso U).inv).1)
    change IsReduced (Spec (CommRingCat.of (Γ(Y, U) ⧸ f.ker.ideal U)))
    infer_instance
  exact @IsReduced.of_openCover _ f.ker.subschemeCover.openCover h

theorem irreducibleSpace_image [IrreducibleSpace Z] : IrreducibleSpace f.image := by
  have h1 : IsIrreducible (Set.range f.toImage) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ Z).image _ f.toImage.continuous.continuousOn
  rw [irreducibleSpace_def, Set.top_eq_univ, ← f.toImage.denseRange.closure_range]
  exact h1.closure

/-- **The scheme-theoretic image of an integral scheme is integral.** -/
theorem isIntegral_image [IsIntegral Z] : IsIntegral f.image := by
  have := isReduced_image f
  have := irreducibleSpace_image f
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end Image

/-! ### Ideal sheaves on affine schemes -/

section Affine

/-- The ideal of `A` of an ideal sheaf on `Spec A`. -/
noncomputable def specIdeal {A : CommRingCat.{u}} (I : (Spec A).IdealSheafData) : Ideal A :=
  (I.ideal ⟨⊤, isAffineOpen_top _⟩).comap (Scheme.ΓSpecIso A).inv.hom

theorem mem_ideal_top_ker_spec_map {A B : CommRingCat.{u}} (g : A ⟶ B) (x : Γ(Spec A, ⊤)) :
    x ∈ (Spec.map g).ker.ideal ⟨⊤, isAffineOpen_top _⟩ ↔
      g ((Scheme.ΓSpecIso A).hom x) = 0 := by
  rw [Scheme.ker_of_isAffine, Scheme.IdealSheafData.ofIdealTop_ideal]
  change x ∈ Ideal.map (𝟙 _ : Γ(Spec A, ⊤) ⟶ Γ(Spec A, ⊤)).hom _ ↔ _
  rw [CommRingCat.hom_id, Ideal.map_id, RingHom.mem_ker]
  have h := congrArg (fun φ => φ.hom x) (Scheme.ΓSpecIso_naturality g)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  rw [← h]
  exact ⟨fun h0 => by rw [h0, map_zero], fun h0 =>
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso B).hom).1 (h0.trans (map_zero _).symm)⟩

/-- The ideal sheaf of `Spec (A/a) ⟶ Spec A` is `a`. -/
theorem specIdeal_ker_spec_map {A : CommRingCat.{u}} (a : Ideal A) :
    specIdeal (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk a))).ker = a := by
  ext y
  rw [specIdeal, Ideal.mem_comap, mem_ideal_top_ker_spec_map]
  change Ideal.Quotient.mk a ((Scheme.ΓSpecIso A).hom ((Scheme.ΓSpecIso A).inv y)) = 0 ↔ _
  rw [Iso.inv_hom_id_apply, Ideal.Quotient.eq_zero_iff_mem]

/-- An ideal sheaf on `Spec A` is the ideal sheaf of `Spec (A / specIdeal I)`. -/
theorem eq_ker_spec_map {A : CommRingCat.{u}} (I : (Spec A).IdealSheafData) :
    I = (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (specIdeal I)))).ker := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  ext x
  rw [mem_ideal_top_ker_spec_map]
  change _ ↔ Ideal.Quotient.mk (specIdeal I) ((Scheme.ΓSpecIso A).hom x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, specIdeal, Ideal.mem_comap, Iso.hom_inv_id_apply]

/-- Pulling back the closed subscheme `Spec (A/a)` along `Spec B ⟶ Spec A` gives `Spec (B/aB)`. -/
theorem comap_ker_spec_map {A B : CommRingCat.{u}} (φ : A ⟶ B) (a : Ideal A) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk a))).ker.comap (Spec.map φ) =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (a.map φ.hom)))).ker := by
  let _ : Algebra A B := φ.hom.toAlgebra
  have := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (Ideal.Quotient.mk a))
    Ideal.Quotient.mk_surjective
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  have e1 : Spec.map φ = Spec.map (CommRingCat.ofHom (algebraMap A B)) := rfl
  have e2 : (CommRingCat.ofHom (Ideal.Quotient.mk a) : A ⟶ CommRingCat.of (A ⧸ a)) =
      CommRingCat.ofHom (algebraMap A (A ⧸ a)) := rfl
  rw [e1, e2, ← pullbackSpecIso_hom_fst' A B (A ⧸ a), Scheme.Hom.ker_comp_of_isIso]
  let e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot B a
  have e3 : CommRingCat.ofHom (algebraMap B (TensorProduct A B (A ⧸ a))) =
      CommRingCat.ofHom (Ideal.Quotient.mk (a.map (algebraMap A B))) ≫
        CommRingCat.ofHom e.toRingEquiv.toRingHom := by
    ext x
    rfl
  have : IsIso (CommRingCat.ofHom e.toRingEquiv.toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr e.bijective
  rw [e3, Spec.map_comp, Scheme.Hom.ker_comp_of_isIso]

/-- **Pulling back along `Spec B ⟶ Spec A` extends the ideal.** -/
theorem specIdeal_comap_spec_map {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (I : (Spec A).IdealSheafData) :
    specIdeal (I.comap (Spec.map φ)) = (specIdeal I).map φ.hom := by
  conv_lhs => rw [eq_ker_spec_map I]
  rw [comap_ker_spec_map, specIdeal_ker_spec_map]

/-- Pulling back along an isomorphism is pushing forward along its inverse. -/
theorem comap_eq_map_inv {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (J : Y.IdealSheafData) :
    J.comap g = J.map (inv g) := by
  rw [Scheme.IdealSheafData.comap, Scheme.IdealSheafData.map]
  have h : pullback.fst g J.subschemeι = pullback.snd g J.subschemeι ≫ J.subschemeι ≫ inv g := by
    rw [← cancel_mono g, Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      pullback.condition]
  rw [h, Scheme.Hom.ker_comp_of_isIso]

theorem ideal_top_comap_of_isIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] [IsAffine X] [IsAffine Y]
    (J : Y.IdealSheafData) :
    (J.comap g).ideal ⟨⊤, isAffineOpen_top _⟩ =
      (J.ideal ⟨⊤, isAffineOpen_top _⟩).comap (inv g).appTop.hom := by
  rw [comap_eq_map_inv, Scheme.IdealSheafData.ideal_map_of_isAffineHom]
  rfl

end Affine

end FlagVarieties.Dimension
