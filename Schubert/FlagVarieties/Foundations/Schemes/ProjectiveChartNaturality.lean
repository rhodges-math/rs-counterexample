import Schubert.FlagVarieties.Foundations.Schemes.ProjectiveLineCompatibility

/-! # Naturality of the homogeneous chart maps -/

noncomputable section

namespace FlagVarieties.Foundations.ProjectiveChartCompatibility

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

universe u

/-- The canonical map from a section's basic open to the corresponding affine localization. -/
def globalBasicOpenMap (X : Scheme.{u}) (r : Γ(X, ⊤)) :
    (X.basicOpen r).toScheme ⟶ Spec (.of (Localization.Away r)) :=
  X.toSpecΓ.resLE (PrimeSpectrum.basicOpen r) (X.basicOpen r)
    (X.toSpecΓ_preimage_basicOpen r).ge ≫ (basicOpenIsoSpecAway r).hom

set_option backward.isDefEq.respectTransparency false in
theorem globalBasicOpenMap_naturality {X Y : Scheme.{u}} (f : Y ⟶ X) (r : Γ(X, ⊤)) :
    f.resLE (X.basicOpen r) (Y.basicOpen (f.appTop r))
      (f.preimage_basicOpen_top r).ge ≫ globalBasicOpenMap X r =
    globalBasicOpenMap Y (f.appTop r) ≫
      Spec.map (CommRingCat.ofHom (Localization.awayMap f.appTop.hom r)) := by
  rw [← cancel_mono (Spec.map (CommRingCat.ofHom
    (algebraMap Γ(X, ⊤) (Localization.Away r))))]
  simp only [globalBasicOpenMap, Category.assoc, basicOpenIsoSpecAway_hom_SpecMap,
    Scheme.Hom.resLE_comp_ι, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hc : (Localization.awayMap f.appTop.hom r).comp
      (algebraMap Γ(X, ⊤) (Localization.Away r)) =
      (algebraMap Γ(Y, ⊤) (Localization.Away (f.appTop r))).comp f.appTop.hom :=
    IsLocalization.map_comp _
  rw [hc, CommRingCat.ofHom_comp, Spec.map_comp]
  simp only [basicOpenIsoSpecAway_hom_SpecMap_assoc, Scheme.Hom.resLE_comp_ι_assoc]
  exact congrArg (fun k => (Y.basicOpen (f.appTop r)).ι ≫ k)
    (Scheme.toSpecΓ_naturality f)

variable {σ : Type*} {A : Type u} [CommRing A]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem evaluatedAwayMap_comp {B C : Type u} [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (t : A) :
    (Localization.awayMap g (f t)).comp (evaluatedAwayMap 𝒜 f t) =
      evaluatedAwayMap 𝒜 (g.comp f) t := by
  unfold evaluatedAwayMap
  rw [← RingHom.comp_assoc]
  congr 1
  apply IsLocalization.ringHom_ext (M := Submonoid.powers t)
  ext a
  simp only [RingHom.comp_apply, Localization.awayMap, IsLocalization.Away.map,
    IsLocalization.map_eq]

set_option backward.isDefEq.respectTransparency false in
theorem toBasicOpen_ι_eq {X : Scheme.{u}} (f : A →+* Γ(X, ⊤))
    {t : A} {d : ℕ} (hd : t ∈ 𝒜 d) (hpos : 0 < d) :
    Proj.toBasicOpenOfGlobalSections 𝒜 f (rfl : f t = f t) hpos hd ≫
      (Proj.basicOpen 𝒜 t).ι =
    globalBasicOpenMap X (f t) ≫
      Spec.map (CommRingCat.ofHom (evaluatedAwayMap 𝒜 f t)) ≫
      Proj.awayι 𝒜 t hd hpos := by
  simp only [Proj.toBasicOpenOfGlobalSections, globalBasicOpenMap, evaluatedAwayMap,
    Scheme.isoOfEq_inv,
    ← Scheme.Hom.resLE_eq_morphismRestrict, CommRingCat.ofHom_comp, Spec.map_comp,
    Scheme.Hom.map_resLE_assoc, Category.assoc, Proj.basicOpenIsoSpec_inv_ι]
  rfl

end FlagVarieties.Foundations.ProjectiveChartCompatibility
