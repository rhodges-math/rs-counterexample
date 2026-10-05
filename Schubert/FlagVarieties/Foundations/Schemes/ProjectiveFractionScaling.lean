import Schubert.FlagVarieties.Foundations.Schemes.ProjectiveChartCompatibility

/-! # Common unit scaling cancels on homogeneous degree-zero fractions -/

noncomputable section

namespace FlagVarieties.Foundations.ProjectiveChartCompatibility

open HomogeneousLocalization

universe u

variable {σ : Type*} {A : Type u} [CommRing A]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  {B : Type u} [CommRing B]

theorem commonAwayMap_mk_mul (f : A →+* B) {t : A} {d : ℕ} (ht : t ∈ 𝒜 d)
    (x y : B) (hxy : x = f t * y) (n : ℕ) (p : A) (hp : p ∈ 𝒜 (n • d)) :
    commonAwayMap 𝒜 f t x y hxy (Away.mk 𝒜 ht n p hp) *
      (algebraMap B (Localization.Away x) (f t)) ^ n =
      algebraMap B (Localization.Away x) (f p) := by
  let : IsLocalization.Away (f t * y) (Localization.Away x) := by rw [← hxy]; infer_instance
  let F : Localization.Away t →+* Localization.Away x :=
    (IsLocalization.Away.awayToAwayRight (f t) y).comp (Localization.awayMap f t)
  have hF (a : A) : F (algebraMap A (Localization.Away t) a) =
      algebraMap B (Localization.Away x) (f a) := by
    dsimp [F, Localization.awayMap, IsLocalization.Away.map]
    rw [IsLocalization.map_eq, IsLocalization.Away.awayToAwayRight_eq]
  have he :
      algebraMap (Away 𝒜 t) (Localization.Away t) (Away.mk 𝒜 ht n p hp) *
        algebraMap A (Localization.Away t) (t ^ n) = algebraMap A (Localization.Away t) p := by
    rw [HomogeneousLocalization.algebraMap_apply, Away.val_mk, Localization.mk_eq_mk']
    exact IsLocalization.mk'_spec (M := Submonoid.powers t) (Localization.Away t) p ⟨t ^ n, n, rfl⟩
  change F _ * _ = _
  simpa only [map_mul, hF, map_pow] using congrArg F he

theorem commonAwayMap_eq_of_homogeneous_unit_scale
    (f g : A →+* B) (u : Bˣ)
    (hscale : ∀ (n : ℕ) (p : A), p ∈ 𝒜 n → g p = (u : B) ^ n * f p)
    {t : A} {d : ℕ} (ht : t ∈ 𝒜 d) :
    commonAwayMap 𝒜 f t (f t * g t) (g t) rfl =
      commonAwayMap 𝒜 g t (f t * g t) (f t) (mul_comm _ _) := by
  ext z
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective 𝒜 ht z
  let L := Localization.Away (f t * g t)
  let a : L := algebraMap B L (f t)
  let b : L := algebraMap B L (f p)
  let c : L := algebraMap B L (u : B)
  have ha : IsUnit a := IsLocalization.Away.isUnit_of_dvd (f t * g t) (dvd_mul_right _ _)
  have hc : IsUnit c := u.isUnit.map (algebraMap B L)
  have hf := commonAwayMap_mk_mul 𝒜 f ht (f t * g t) (g t) rfl n p hp
  have hg := commonAwayMap_mk_mul 𝒜 g ht (f t * g t) (f t) (mul_comm _ _) n p hp
  have hgt : algebraMap B L (g t) = c ^ d * a := by
    calc
      algebraMap B L (g t) = algebraMap B L ((u : B) ^ d * f t) :=
        congrArg (algebraMap B L) (hscale d t ht)
      _ = c ^ d * a := by simp only [map_mul, map_pow]; rfl
  have hgp : algebraMap B L (g p) = c ^ (n * d) * b := by
    calc
      algebraMap B L (g p) = algebraMap B L ((u : B) ^ (n • d) * f p) :=
        congrArg (algebraMap B L) (hscale (n • d) p hp)
      _ = c ^ (n * d) * b := by simp only [map_mul, map_pow]; rfl
  rw [hgt, hgp] at hg
  have hg' : commonAwayMap 𝒜 g t (f t * g t) (f t) (mul_comm _ _)
      (Away.mk 𝒜 ht n p hp) * a ^ n = b := by
    apply (hc.pow (n * d)).mul_left_cancel
    calc
      c ^ (n * d) * (commonAwayMap 𝒜 g t (f t * g t) (f t) (mul_comm _ _)
          (Away.mk 𝒜 ht n p hp) * a ^ n) =
        commonAwayMap 𝒜 g t (f t * g t) (f t) (mul_comm _ _)
          (Away.mk 𝒜 ht n p hp) * (c ^ d * a) ^ n := by
            rw [mul_pow, ← pow_mul, Nat.mul_comm d n]
            ring
      _ = c ^ (n * d) * b := hg
  exact (ha.pow n).mul_right_cancel (hf.trans hg'.symm)

end FlagVarieties.Foundations.ProjectiveChartCompatibility
