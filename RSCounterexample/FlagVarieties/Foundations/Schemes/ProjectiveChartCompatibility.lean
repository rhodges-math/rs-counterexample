import RSCounterexample.FlagVarieties.Foundations.Schemes.ProjectiveLineScaling

/-! # Restricting the Proj chart morphisms to a common basic open -/

noncomputable section

namespace FlagVarieties.Foundations.ProjectiveChartCompatibility

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

universe u

variable {σ : Type*} {A : Type u} [CommRing A]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

variable {B : Type u} [CommRing B]

/-- The map on a homogeneous chart obtained by evaluating fractions. -/
def evaluatedAwayMap (f : A →+* B) (t : A) :
    Away 𝒜 t →+* Localization.Away (f t) :=
  (Localization.awayMap f t).comp (algebraMap (Away 𝒜 t) (Localization.Away t))

/-- The same chart map with its target localized at a multiple of the evaluated denominator. -/
def commonAwayMap (f : A →+* B) (t : A) (x y : B) (hxy : x = f t * y) :
    Away 𝒜 t →+* Localization.Away x :=
  letI : IsLocalization.Away (f t * y) (Localization.Away x) := by
    rw [← hxy]
    infer_instance
  (IsLocalization.Away.awayToAwayRight (f t) y).comp (evaluatedAwayMap 𝒜 f t)

variable {X : Scheme.{u}} (f : A →+* Γ(X, ⊤)) {t : A} {d : ℕ}
  (hd : t ∈ 𝒜 d) (hpos : 0 < d)

set_option backward.isDefEq.respectTransparency false in
theorem restrict_toBasicOpen_mul (y : Γ(X, ⊤)) :
    X.homOfLE (by rw [Scheme.basicOpen_mul]; exact inf_le_left) ≫
      Proj.toBasicOpenOfGlobalSections 𝒜 f (rfl : f t = f t) hpos hd ≫
      (Proj.basicOpen 𝒜 t).ι =
    (X.isoOfEq (X.toSpecΓ_preimage_basicOpen (f t * y))).inv ≫
      X.toSpecΓ ∣_ (PrimeSpectrum.basicOpen (f t * y)) ≫
      (basicOpenIsoSpecAway (f t * y)).hom ≫
      Spec.map (CommRingCat.ofHom (commonAwayMap 𝒜 f t (f t * y) y rfl)) ≫
      Proj.awayι 𝒜 t hd hpos := by
  simp only [Proj.toBasicOpenOfGlobalSections, Scheme.isoOfEq_inv,
    ← Scheme.Hom.resLE_eq_morphismRestrict, CommRingCat.ofHom_comp, Spec.map_comp,
    Scheme.Hom.map_resLE_assoc, Category.assoc, Proj.basicOpenIsoSpec_inv_ι]
  have hle : PrimeSpectrum.basicOpen (f t * y) ≤ PrimeSpectrum.basicOpen (f t) := by
    rw [PrimeSpectrum.basicOpen_mul]
    exact inf_le_left
  rw [← Scheme.Hom.resLE_map_assoc _ (by simp [X.toSpecΓ_preimage_basicOpen]) hle]
  congr 1
  rw [← cancel_epi (basicOpenIsoSpecAway (f t * y)).inv]
  simp only [Iso.inv_hom_id_assoc]
  rw [basicOpenIsoSpecAway_inv_homOfLE_assoc (f t) y (f t * y) rfl]
  simp only [Iso.inv_hom_id_assoc]
  simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem restrict_toBasicOpen_common (x y : Γ(X, ⊤)) (hxy : x = f t * y) :
    X.homOfLE (by rw [hxy, Scheme.basicOpen_mul]; exact inf_le_left) ≫
      Proj.toBasicOpenOfGlobalSections 𝒜 f (rfl : f t = f t) hpos hd ≫
      (Proj.basicOpen 𝒜 t).ι =
    (X.isoOfEq (X.toSpecΓ_preimage_basicOpen x)).inv ≫
      X.toSpecΓ ∣_ (PrimeSpectrum.basicOpen x) ≫
      (basicOpenIsoSpecAway x).hom ≫
      Spec.map (CommRingCat.ofHom (commonAwayMap 𝒜 f t x y hxy)) ≫
      Proj.awayι 𝒜 t hd hpos := by
  subst x
  exact restrict_toBasicOpen_mul 𝒜 f hd hpos y

end FlagVarieties.Foundations.ProjectiveChartCompatibility
