import RSCounterexample.FlagVarieties.Foundations.Schemes.ProjectiveChartNaturality

/-!
# Pullback naturality of the ordered quotient-coordinate morphism

The equality concerns full scheme morphisms. Coprimality of the pulled-back
global sections follows by applying the map on global sections to the supplied
Bézout identity; no sheaf-generation-to-global-coprimality assertion is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

universe u

namespace FlagVarieties.Foundations.ProjectiveChartCompatibility

variable {σ : Type*} {A : Type u} [CommRing A]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  {X Y : Scheme.{u}} (a : A →+* Γ(X, ⊤))
  (ha : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map a = ⊤)

include ha in
theorem map_irrelevant_comp_eq_top (f : Y ⟶ X) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (f.appTop.hom.comp a) = ⊤ := by
  rw [← Ideal.map_map, ha, Ideal.map_top]

set_option backward.isDefEq.respectTransparency false in
theorem basicOpen_ι_fromOfGlobalSections_eq {t : A} {d : ℕ}
    (hd : t ∈ 𝒜 d) (hpos : 0 < d) :
    (X.basicOpen (a t)).ι ≫ Proj.fromOfGlobalSections 𝒜 a ha =
      globalBasicOpenMap X (a t) ≫
        Spec.map (CommRingCat.ofHom (evaluatedAwayMap 𝒜 a t)) ≫
        Proj.awayι 𝒜 t hd hpos := by
  rw [← Scheme.Hom.resLE_comp_ι _
    (Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 a ha hpos hd).ge,
    Proj.fromOfGlobalSections_resLE, toBasicOpen_ι_eq]

set_option backward.isDefEq.respectTransparency false in
theorem fromOfGlobalSections_naturality (f : Y ⟶ X) :
    f ≫ Proj.fromOfGlobalSections 𝒜 a ha =
      Proj.fromOfGlobalSections 𝒜 (f.appTop.hom.comp a)
        (map_irrelevant_comp_eq_top 𝒜 a ha f) := by
  apply (Proj.openCoverOfMapIrrelevantEqTop 𝒜 (f.appTop.hom.comp a)
    (map_irrelevant_comp_eq_top 𝒜 a ha f)).hom_ext
  rintro ⟨d, t, hpos, ht⟩
  change (Y.basicOpen (f.appTop (a t))).ι ≫ f ≫ Proj.fromOfGlobalSections 𝒜 a ha =
    (Y.basicOpen (f.appTop (a t))).ι ≫ _
  rw [← Scheme.Hom.resLE_comp_ι_assoc f (f.preimage_basicOpen_top (a t)).ge,
    basicOpen_ι_fromOfGlobalSections_eq 𝒜 a ha ht hpos]
  trans globalBasicOpenMap Y (f.appTop (a t)) ≫
    Spec.map (CommRingCat.ofHom (evaluatedAwayMap 𝒜 (f.appTop.hom.comp a) t)) ≫
    Proj.awayι 𝒜 t ht hpos
  · simp only [← Category.assoc]
    rw [globalBasicOpenMap_naturality]
    simp only [Category.assoc]
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, evaluatedAwayMap_comp]
  · exact (basicOpen_ι_fromOfGlobalSections_eq 𝒜 (f.appTop.hom.comp a)
      (map_irrelevant_comp_eq_top 𝒜 a ha f) ht hpos).symm

end FlagVarieties.Foundations.ProjectiveChartCompatibility

namespace FlagVarieties.Foundations.ProjectiveLine

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}

theorem evaluation_comp (φ : R →+* Γ(X, ⊤)) (δ ε : Γ(X, ⊤)) (f : Y ⟶ X) :
    f.appTop.hom.comp (evaluation φ δ ε) =
      evaluation (f.appTop.hom.comp φ) (f.appTop δ) (f.appTop ε) := by
  ext r
  · simp only [RingHom.comp_apply, evaluation_C]
  · fin_cases r <;> simp only [RingHom.comp_apply, evaluation_X] <;> rfl

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Pulling back a globally unimodular ordered pair pulls back its Proj morphism. -/
theorem fromPair_naturality (φ : R →+* Γ(X, ⊤)) (δ ε : Γ(X, ⊤))
    (h : IsCoprime δ ε) (f : Y ⟶ X) :
    f ≫ fromPair φ δ ε h =
      fromPair (f.appTop.hom.comp φ) (f.appTop δ) (f.appTop ε) (h.map f.appTop.hom) := by
  unfold fromPair
  rw [ProjectiveChartCompatibility.fromOfGlobalSections_naturality]
  congr 1
  exact evaluation_comp φ δ ε f

end FlagVarieties.Foundations.ProjectiveLine
