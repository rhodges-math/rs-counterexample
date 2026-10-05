import Schubert.FlagVarieties.Plucker.ProjSpace
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# The structure morphism of `ℙ(R^σ)` and morphisms through a standard chart

* `projToSpec R σ : ℙ(R^σ) ⟶ Spec R`, proper for finite `σ` (`Proj` properness of Mathlib, as in
  `Foundations/Schemes/ProjectiveSpaceProper`), and
  `fromSections_toSpec`: `fromSections φ s h` is a morphism over `Spec R`.
* `exists_fromSections_eq_awayι`: on an affine scheme `Spec C` where the coordinate `s_t` is a
  unit, `fromSections φ s h` factors as `Spec ψ` followed by the standard chart
  `Spec (R[X]_{(X_t)}) ⟶ ℙ(R^σ)`, where `ψ` evaluates the homogeneous fractions:
  `ψ(p / X_t^m) · s_t^m = p(s)`.
-/

noncomputable section

namespace FlagVarieties.Plucker

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open Foundations.ProjectiveChartCompatibility

universe u

variable {R : Type u} [CommRing R] {σ : Type}

/-! ### The structure morphism -/

variable (R σ) in
/-- The constants `R → (R[X_i])₀`. -/
def coeffZero : R →+* grading R σ 0 where
  toFun c := ⟨MvPolynomial.C c, MvPolynomial.isHomogeneous_C σ c⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' a b := by ext; simp
  map_mul' a b := by ext; simp

theorem coeffZero_bijective : Function.Bijective (coeffZero R σ) := by
  constructor
  · intro r s h
    exact MvPolynomial.C_injective σ R (congrArg Subtype.val h)
  · intro p
    have hp : (p : MvPolynomial σ R).totalDegree = 0 :=
      (MvPolynomial.totalDegree_zero_iff_isHomogeneous σ).mpr p.property
    exact ⟨(p : MvPolynomial σ R).coeff 0,
      Subtype.ext (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hp).symm⟩

instance : IsIso (CommRingCat.ofHom (coeffZero R σ)) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr coeffZero_bijective

variable (R σ) in
/-- **The structure morphism `ℙ(R^σ) ⟶ Spec R`**. -/
def projToSpec : projSpace R σ ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (grading R σ) ≫ Spec.map (CommRingCat.ofHom (coeffZero R σ))

theorem finiteType_zero [Finite σ] :
    Algebra.FiniteType (grading R σ 0) (MvPolynomial σ R) := by
  let : Algebra R (grading R σ 0) := (coeffZero R σ).toAlgebra
  let : SMul R (grading R σ 0) := Algebra.toSMul
  let : IsScalarTower R (grading R σ 0) (MvPolynomial σ R) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact Algebra.FiniteType.of_restrictScalars_finiteType R (grading R σ 0) (MvPolynomial σ R)

/-- **`ℙ(R^σ)` is proper over `R`** for finite `σ`. -/
instance isProper_projToSpec [Finite σ] : IsProper (projToSpec R σ) := by
  have := finiteType_zero (R := R) (σ := σ)
  unfold projToSpec
  infer_instance

/-- `fromSections φ s h` lies over `Spec R`. -/
theorem fromSections_toSpec {X : Scheme.{u}} (φ : R →+* Γ(X, ⊤)) (s : σ → Γ(X, ⊤))
    (h : Ideal.span (Set.range s) = ⊤) :
    fromSections φ s h ≫ projToSpec R σ = X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) := by
  rw [projToSpec, fromSections, Proj.fromOfGlobalSections_toSpecZero_assoc, ← Spec.map_comp]
  congr 2
  ext r
  simp [coeffZero, evalSections]

/-! ### Factoring through a standard chart -/

theorem evaluatedAwayMap_mk_mul {B : Type u} [CommRing B] (f : MvPolynomial σ R →+* B)
    {t : MvPolynomial σ R} {d : ℕ} (ht : t ∈ grading R σ d) (m : ℕ) (p : MvPolynomial σ R)
    (hp : p ∈ grading R σ (m • d)) :
    evaluatedAwayMap (grading R σ) f t (Away.mk (grading R σ) ht m p hp) *
      (algebraMap B (Localization.Away (f t)) (f t)) ^ m =
      algebraMap B (Localization.Away (f t)) (f p) := by
  have hF (a : MvPolynomial σ R) :
      Localization.awayMap f t (algebraMap _ (Localization.Away t) a) =
        algebraMap B (Localization.Away (f t)) (f a) := by
    simp only [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  have he : algebraMap (Away (grading R σ) t) (Localization.Away t)
      (Away.mk (grading R σ) ht m p hp) * algebraMap _ (Localization.Away t) (t ^ m) =
      algebraMap _ (Localization.Away t) p := by
    rw [HomogeneousLocalization.algebraMap_apply, Away.val_mk, Localization.mk_eq_mk']
    exact IsLocalization.mk'_spec (M := Submonoid.powers t) (Localization.Away t) p ⟨t ^ m, m, rfl⟩
  have := congrArg (Localization.awayMap f t) he
  rw [map_mul, hF, hF] at this
  change Localization.awayMap f t (algebraMap (Away (grading R σ) t) (Localization.Away t)
    (Away.mk (grading R σ) ht m p hp)) * _ = _
  simpa only [map_pow] using this

set_option backward.isDefEq.respectTransparency false in
/-- **Through the chart of a unit coordinate.** On `Spec C`, if `s_t` is a unit, then
`fromSections φ s h` factors through the standard chart `Spec R[X]_{(X_t)} ⟶ ℙ(R^σ)` by a ring map
`ψ` with `ψ(p / X_t^m) · s_t^m = p(s)`. -/
theorem exists_fromSections_eq_awayι {C : CommRingCat.{u}} (φ : R →+* Γ(Spec C, ⊤))
    (s : σ → Γ(Spec C, ⊤)) (h : Ideal.span (Set.range s) = ⊤) (t : σ) (ht : IsUnit (s t)) :
    ∃ ψ : CommRingCat.of (Away (grading R σ) (MvPolynomial.X t)) ⟶ C,
      fromSections φ s h = Spec.map ψ ≫
        Proj.awayι (grading R σ) (MvPolynomial.X t) (X_mem_grading_one t) Nat.one_pos ∧
      ∀ (m : ℕ) (p : MvPolynomial σ R) (hp : p ∈ grading R σ (m • 1)),
        ψ (Away.mk (grading R σ) (X_mem_grading_one t) m p hp) *
            (Scheme.ΓSpecIso C).hom (s t) ^ m =
          (Scheme.ΓSpecIso C).hom (evalSections φ s p) := by
  have hat : evalSections φ s (MvPolynomial.X t) = s t := evalSections_X φ s t
  have hF := basicOpen_ι_fromOfGlobalSections_eq (grading R σ) (evalSections φ s)
    (map_irrelevant_eq_top φ s h) (X_mem_grading_one t) Nat.one_pos
  have hU : (Spec C).basicOpen (evalSections φ s (MvPolynomial.X t)) = ⊤ :=
    Scheme.basicOpen_of_isUnit _ (hat ▸ ht)
  let κ : Spec C ⟶ ((Spec C).basicOpen (evalSections φ s (MvPolynomial.X t))).toScheme :=
    (Spec C).topIso.inv ≫ ((Spec C).isoOfEq hU).inv
  have hκ : κ ≫ ((Spec C).basicOpen (evalSections φ s (MvPolynomial.X t))).ι = 𝟙 _ := by
    simp only [κ, Category.assoc, Scheme.isoOfEq_inv_ι, Scheme.toIso_inv_ι]
  let G := globalBasicOpenMap (Spec C) (evalSections φ s (MvPolynomial.X t))
  let χ := Spec.preimage (κ ≫ G)
  have hχ : Spec.map χ = κ ≫ G := Spec.map_preimage _
  refine ⟨CommRingCat.ofHom (evaluatedAwayMap (grading R σ) (evalSections φ s)
    (MvPolynomial.X t)) ≫ χ, ?_, ?_⟩
  · rw [Spec.map_comp, hχ, Category.assoc, Category.assoc, ← hF, ← Category.assoc, hκ,
      Category.id_comp, fromSections]
  · intro m p hp
    have halg : CommRingCat.ofHom (algebraMap Γ(Spec C, ⊤)
        (Localization.Away (evalSections φ s (MvPolynomial.X t)))) ≫ χ =
        (Scheme.ΓSpecIso C).hom := by
      apply Spec.map_injective
      have hG : G ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(Spec C, ⊤)
          (Localization.Away (evalSections φ s (MvPolynomial.X t))))) =
          ((Spec C).basicOpen (evalSections φ s (MvPolynomial.X t))).ι ≫ (Spec C).toSpecΓ := by
        simp only [G, globalBasicOpenMap, Category.assoc, basicOpenIsoSpecAway_hom_SpecMap,
          Scheme.Hom.resLE_comp_ι]
      rw [Spec.map_comp, hχ, SpecMap_ΓSpecIso_hom, Category.assoc, hG, ← Category.assoc, hκ,
        Category.id_comp]
    have hθ : ∀ x, χ (algebraMap Γ(Spec C, ⊤)
        (Localization.Away (evalSections φ s (MvPolynomial.X t))) x) =
        (Scheme.ΓSpecIso C).hom x := fun x => by
      rw [← halg]
      rfl
    have key := congrArg χ (evaluatedAwayMap_mk_mul (evalSections φ s) (X_mem_grading_one t) m p hp)
    rw [map_mul, map_pow, hθ, hθ] at key
    rw [← hat]
    exact key

end FlagVarieties.Plucker
