import RSCounterexample.FlagVarieties.Foundations.Schemes.ProjectiveFractionScaling

/-!
# Full scheme-morphism invariance under a common unit

The proof compares the maps on homogeneous affine charts. The
numerator and denominator scaling factors cancel in the localization,
and equality on the source open cover yields equality of scheme morphisms.
Global coprimality is an explicit hypothesis of the ordered-pair
construction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

universe u

namespace FlagVarieties.Foundations.ProjectiveChartCompatibility

variable {σ : Type*} {A : Type u} [CommRing A]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  {X : Scheme.{u}} (f : A →+* Γ(X, ⊤))
  (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
  {t : A} {d : ℕ} (hd : t ∈ 𝒜 d) (hpos : 0 < d)

set_option backward.isDefEq.respectTransparency false in
theorem restrict_fromOfGlobalSections_common (x y : Γ(X, ⊤)) (hxy : x = f t * y) :
    (X.basicOpen x).ι ≫ Proj.fromOfGlobalSections 𝒜 f hf =
    (X.isoOfEq (X.toSpecΓ_preimage_basicOpen x)).inv ≫
      X.toSpecΓ ∣_ (PrimeSpectrum.basicOpen x) ≫
      (basicOpenIsoSpecAway x).hom ≫
      Spec.map (CommRingCat.ofHom (commonAwayMap 𝒜 f t x y hxy)) ≫
      Proj.awayι 𝒜 t hd hpos := by
  rw [← restrict_toBasicOpen_common 𝒜 f hd hpos x y hxy,
    ← Proj.fromOfGlobalSections_resLE 𝒜 f hf hpos hd]
  simp only [Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem fromOfGlobalSections_eq_of_homogeneous_unit_scale
    (g : A →+* Γ(X, ⊤)) (hg : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map g = ⊤)
    (u : Γ(X, ⊤)ˣ)
    (hscale : ∀ (n : ℕ) (p : A), p ∈ 𝒜 n → g p = (u : Γ(X, ⊤)) ^ n * f p) :
    Proj.fromOfGlobalSections 𝒜 f hf = Proj.fromOfGlobalSections 𝒜 g hg := by
  apply (Proj.openCoverOfMapIrrelevantEqTop 𝒜 f hf).hom_ext
  rintro ⟨d, t, hpos, ht⟩
  change (X.basicOpen (f t)).ι ≫ _ = (X.basicOpen (f t)).ι ≫ _
  have hgt : X.basicOpen (g t) = X.basicOpen (f t) := by
    rw [hscale d t ht, Scheme.basicOpen_mul,
      X.basicOpen_of_isUnit (u.isUnit.pow d)]
    simp
  have hopen : X.basicOpen (f t * g t) = X.basicOpen (f t) := by
    rw [Scheme.basicOpen_mul, hgt, inf_idem]
  rw [← cancel_epi (X.isoOfEq hopen).hom]
  simp only [← Category.assoc, Scheme.isoOfEq_hom_ι]
  rw [restrict_fromOfGlobalSections_common 𝒜 f hf ht hpos (f t * g t) (g t) rfl,
    restrict_fromOfGlobalSections_common 𝒜 g hg ht hpos (f t * g t) (f t) (mul_comm _ _),
    commonAwayMap_eq_of_homogeneous_unit_scale 𝒜 f g u hscale ht]

end FlagVarieties.Foundations.ProjectiveChartCompatibility

namespace FlagVarieties.Foundations.ProjectiveLine

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (φ : R →+* Γ(X, ⊤)) (δ ε : Γ(X, ⊤)) (h : IsCoprime δ ε) (u : Γ(X, ⊤)ˣ)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Common unit rescaling leaves the full scheme morphism unchanged. -/
theorem fromPair_unit_mul :
    fromPair φ ((u : Γ(X, ⊤)) * δ) ((u : Γ(X, ⊤)) * ε) (isCoprime_unit_scale δ ε h u) =
      fromPair φ δ ε h := by
  exact (ProjectiveChartCompatibility.fromOfGlobalSections_eq_of_homogeneous_unit_scale
    (grading R) (evaluation φ δ ε) (map_irrelevant_eq_top φ δ ε h)
    (evaluation φ ((u : Γ(X, ⊤)) * δ) ((u : Γ(X, ⊤)) * ε))
    (map_irrelevant_eq_top φ _ _ (isCoprime_unit_scale δ ε h u)) u
    (fun n p hp => evaluation_scale_of_homogeneous φ δ ε (u : Γ(X, ⊤)) hp)).symm

end FlagVarieties.Foundations.ProjectiveLine
