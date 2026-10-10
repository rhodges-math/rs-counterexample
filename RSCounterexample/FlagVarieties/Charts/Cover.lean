import RSCounterexample.FlagVarieties.Charts.BigCellFunction
import RSCounterexample.FlagVarieties.Charts.FieldCover

/-!
# The big cells cover the flag scheme

* `FlagVarieties.exists_factor_bigCellChart_iff`: a point `g` of `GLₙ` (with values in any ring)
  maps into the big cell of `v` under the orbit map iff `f_v(g)` is a unit.
* `FlagVarieties.mem_bigCell_iff`: a point of `GLₙ`, given by a prime `p` of `𝒪(GLₙ)`, maps
  into the big cell of `v` iff `f_v ∉ p`; i.e. `π⁻¹(bigCell v) = D(f_v)`.
* `FlagVarieties.exists_mem_bigCell`: every point of `Flₙ` lies in some big cell.
* `FlagVarieties.span_bigCellFunction`: the functions `f_v` generate the unit ideal of `𝒪(GLₙ)`.
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory
open Foundations Foundations.QuotientCharts

universe u

variable (R : Type u) [CommRing R] {n : ℕ}

/-- The orbit map, read on `Spec 𝒪(GLₙ)`. -/
abbrev specOrbitMap : Spec (CommRingCat.of (GLCoord R n)) ⟶ FlagScheme R n :=
  (TauCeti.GeneralLinear.groupSchemeSpecIso R n).inv ≫ FlagScheme.orbitMap R n

variable {R}

/-- A point `g` of `GLₙ` maps into the big cell of `v` iff `f_v(g)` is a unit. -/
theorem exists_factor_bigCellChart_iff {A : Type u} [CommRing A] [Algebra R A]
    (v : Equiv.Perm (Fin n)) (φ : GLCoord R n →ₐ[R] A) :
    (∃ g, g ≫ bigCellChart R v = GLScheme.point R n φ ≫ FlagScheme.orbitMap R n) ↔
      IsUnit (φ (bigCellFunction R v)) := by
  rw [FlagScheme.orbitMap_point, isUnit_map_bigCellFunction_iff]
  constructor
  · rintro ⟨g, hg⟩
    exact inBigCell_of_factors v _ g hg
  · intro hP
    exact exists_factor_of_inBigCell v _ hP

/-- A morphism from the spectrum of a field lands in an open subscheme iff it factors through it. -/
theorem exists_factor_iff_mem {K : Type u} [Field K] {X U : Scheme.{u}} (ι : U ⟶ X)
    [IsOpenImmersion ι] (h : Spec (CommRingCat.of K) ⟶ X) (pt : Spec (CommRingCat.of K)) :
    (∃ g, g ≫ ι = h) ↔ h pt ∈ Set.range ι := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g pt, rfl⟩
  · intro hx
    have hr : Set.range h ⊆ Set.range ι := by
      rintro _ ⟨y, rfl⟩
      have : y = pt := Subsingleton.elim _ _
      rw [this]
      exact hx
    exact ⟨IsOpenImmersion.lift ι h hr, IsOpenImmersion.lift_fac ι h hr⟩

/-- **`π⁻¹(bigCell v) = D(f_v)`.** -/
theorem mem_bigCell_iff (v : Equiv.Perm (Fin n)) (p : PrimeSpectrum (GLCoord R n)) :
    specOrbitMap R p ∈ bigCell R v ↔ bigCellFunction R v ∉ p.asIdeal := by
  have : p.asIdeal.IsPrime := p.isPrime
  let φ : GLCoord R n →ₐ[R] p.asIdeal.ResidueField :=
    IsScalarTower.toAlgHom R (GLCoord R n) p.asIdeal.ResidueField
  let pt : Spec (CommRingCat.of p.asIdeal.ResidueField) :=
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum p.asIdeal.ResidueField)
  have hpt : (Spec.map (CommRingCat.ofHom φ.toRingHom)) pt = p := by
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap (GLCoord R n) p.asIdeal.ResidueField) ⊥ = p.asIdeal
    rw [← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]
  have hp : (GLScheme.point R n φ ≫ FlagScheme.orbitMap R n) pt = specOrbitMap R p := by
    change (FlagScheme.orbitMap R n) ((TauCeti.GeneralLinear.groupSchemeSpecIso R n).inv
      ((Spec.map (CommRingCat.ofHom φ.toRingHom)) pt)) = _
    rw [hpt]
    rfl
  have key := exists_factor_iff_mem (bigCellChart R v)
    (GLScheme.point R n φ ≫ FlagScheme.orbitMap R n) pt
  rw [exists_factor_bigCellChart_iff, hp] at key
  change specOrbitMap R p ∈ Set.range (bigCellChart R v) ↔ _
  rw [← key, isUnit_iff_ne_zero, ne_eq]
  exact not_congr Ideal.algebraMap_residueField_eq_zero

/-- Over a field, the step `Vⱼ` of a coordinate flag has dimension `j`. -/
theorem finrank_step {K : Type u} [Field K] (P : CoordinateFlag K n) (j : Fin (n + 1)) :
    Module.finrank K (P.step j).toSubmodule = j.val := by
  have h := (P.step j).rankAtStalk_eq ⊥
  simp only [Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Nat.cast_id] at h
  have h2 := Submodule.finrank_quotient_add_finrank (P.step j).toSubmodule
  rw [h, Module.finrank_fin_fun] at h2
  have := j.isLt
  omega

/-- Every complete flag over a field lies in some big cell. -/
theorem exists_inBigCell {K : Type u} [Field K] (P : CoordinateFlag K n) :
    ∃ v : Equiv.Perm (Fin n), InBigCell v P := by
  obtain ⟨v, hv⟩ := exists_perm_isCompl_tailSpan (flagSteps P) (flagSteps_monotone P)
    (fun j hj => by
      rw [flagSteps_of_le P hj]
      exact finrank_step P ⟨j, Nat.lt_succ_of_le hj⟩)
  refine ⟨v, fun j => ?_⟩
  have hj := Nat.lt_succ_iff.mp j.isLt
  have := hv j.val hj
  rwa [flagSteps_of_le P hj] at this

/-- Every point of `Flₙ` with values in a field factors through some big cell. -/
theorem exists_factor_of_field {K : Type u} [Field K] [Algebra R K]
    (h : Spec (CommRingCat.of K) ⟶ FlagScheme R n)
    (hh : h ≫ FlagScheme.toSpec R n = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃ (v : Equiv.Perm (Fin n)) (g : Spec (CommRingCat.of K) ⟶ bigCellChartScheme R v),
      g ≫ bigCellChart R v = h := by
  obtain ⟨P, hP⟩ := FlagScheme.exists_eq_ofRingFlag h hh
  obtain ⟨v, hv⟩ := exists_inBigCell P
  obtain ⟨g, hg⟩ := exists_factor_of_inBigCell (R := R) v P hv
  exact ⟨v, g, hg.trans hP⟩

variable (R) in
/-- **The big cells cover `Flₙ`.** -/
theorem exists_mem_bigCell (x : FlagScheme R n) : ∃ v : Equiv.Perm (Fin n), x ∈ bigCell R v := by
  let ψ := Spec.preimage ((FlagScheme R n).fromSpecResidueField x ≫ FlagScheme.toSpec R n)
  let : Algebra R ((FlagScheme R n).residueField x) := ψ.hom.toAlgebra
  obtain ⟨v, g, hg⟩ := exists_factor_of_field (K := (FlagScheme R n).residueField x)
    ((FlagScheme R n).fromSpecResidueField x) (Spec.map_preimage _).symm
  have hx : x ∈ Set.range ((FlagScheme R n).fromSpecResidueField x) := by
    rw [Scheme.range_fromSpecResidueField]
    rfl
  obtain ⟨pt, hpt⟩ := hx
  refine ⟨v, ⟨g pt, ?_⟩⟩
  exact ((Scheme.Hom.comp_apply _ _ _).symm.trans
    (congrArg (fun f : Spec _ ⟶ FlagScheme R n => f pt) hg)).trans hpt

variable (R n) in
/-- The functions `f_v` generate the unit ideal of `𝒪(GLₙ)`: the open sets `D(f_v)` cover `GLₙ`. -/
theorem span_bigCellFunction :
    Ideal.span (Set.range (bigCellFunction (n := n) R)) = ⊤ := by
  rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff, eq_top_iff]
  intro p _
  obtain ⟨v, hv⟩ := exists_mem_bigCell R (specOrbitMap R p)
  rw [TopologicalSpace.Opens.mem_iSup]
  exact ⟨v, (mem_bigCell_iff v p).mp hv⟩

end FlagVarieties
