import RSCounterexample.FlagVarieties.Foundations.Schemes.GlobalQuotientFlagNaturality
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedFlagSeparated
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedFlagFiniteType
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedFlagAffineRingClassification
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedFlagGlobalFaithfulness
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedQuotientMorphismNaturality
import RSCounterexample.FlagVarieties.Foundations.Flags.RingBasisBaseChange

/-!
# The complete flag scheme

This file is the public interface to the complete flag scheme of the foundations.

* `FlagVarieties.FlagScheme R n`: the scheme `Flₙ` over `Spec R`, for a commutative ring `R`.
  It is glued from affine incidence charts.
* `FlagVarieties.CoordinateFlag A n`: complete flags `0 = V₀ ⊆ V₁ ⊆ ⋯ ⊆ Vₙ = Aⁿ` of submodules
  of `Aⁿ` whose quotients `Aⁿ / Vⱼ` are finite projective of constant rank `n - j`.
* `FlagScheme.pointEquiv`: for an `R`-algebra `A`, the morphisms `Spec A ⟶ Flₙ` over `Spec R`
  are exactly the coordinate flags over `A`.
* `FlagScheme.existsUnique_classify`: over an arbitrary `R`-scheme `X`, every complete flag of
  locally free quotients of `𝒪ₓⁿ` is pulled back from the universal one along a unique morphism.
* `FlagScheme.ofRingFlag_baseChange`: the classifying points are natural in the ring.
* `FlagScheme.standardFlag`: the point of the standard flag `Vⱼ = span(e₁, …, eⱼ)`.
* `Flₙ ⟶ Spec R` is separated, quasi-compact and locally of finite type.
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Foundations Foundations.QuotientCharts

universe u

/-- Complete flags of `Aⁿ` with finite projective quotients: `step j` is a submodule `Vⱼ` with
`Aⁿ / Vⱼ` finite projective of rank `n - j`, `V₀ = 0`, `Vₙ = Aⁿ`, and `Vᵢ ⊆ Vⱼ` for `i ≤ j`. -/
abbrev CoordinateFlag (A : Type u) [CommRing A] (n : ℕ) : Type u :=
  RingFlag A (Fin n → A) n

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The complete flag scheme `Flₙ` over `Spec R`. -/
abbrev FlagScheme : Scheme.{u} :=
  selectedFlagChartScheme R n

namespace FlagScheme

/-- The structure morphism `Flₙ ⟶ Spec R`. -/
abbrev toSpec : FlagScheme R n ⟶ Spec (CommRingCat.of R) :=
  selectedFlagChartSchemeToSpec R n

theorem isSeparated_toSpec : IsSeparated (toSpec R n) := inferInstance

theorem locallyOfFiniteType_toSpec : LocallyOfFiniteType (toSpec R n) := inferInstance

theorem quasiCompact_toSpec : QuasiCompact (toSpec R n) := inferInstance

/-! ### Points with values in rings -/

variable {R n}

/-- The `A`-point of `Flₙ` classifying a coordinate flag over the `R`-algebra `A`. -/
def ofRingFlag (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (P : CoordinateFlag A n) : Spec (CommRingCat.of A) ⟶ FlagScheme R n :=
  simultaneousFlagRelativeMorphism R P

@[reassoc (attr := simp)] theorem ofRingFlag_toSpec {A : Type u} [CommRing A] [Algebra R A]
    (P : CoordinateFlag A n) :
    ofRingFlag R P ≫ toSpec R n = Spec.map (CommRingCat.ofHom (algebraMap R A)) :=
  simultaneousFlagRelativeMorphism_toSpec R P

variable (R n) in
/-- The `A`-points of `Flₙ` over `Spec R` are the coordinate flags over `A`. -/
def pointEquiv (A : Type u) [CommRing A] [Algebra R A] :
    CoordinateFlag A n ≃
      {f : Spec (CommRingCat.of A) ⟶ FlagScheme R n //
        f ≫ toSpec R n = Spec.map (CommRingCat.ofHom (algebraMap R A))} :=
  selectedFlagAffineRingEquiv R (CommRingCat.of A) n

theorem pointEquiv_apply_coe {A : Type u} [CommRing A] [Algebra R A] (P : CoordinateFlag A n) :
    (pointEquiv R n A P).val = ofRingFlag R P := rfl

theorem ofRingFlag_injective {A : Type u} [CommRing A] [Algebra R A] :
    Function.Injective (ofRingFlag R : CoordinateFlag A n → _) := by
  intro P Q h
  apply (pointEquiv R n A).injective
  exact Subtype.ext h

/-- Every `A`-point over `Spec R` is the classifying point of a coordinate flag. -/
theorem exists_eq_ofRingFlag {A : Type u} [CommRing A] [Algebra R A]
    (f : Spec (CommRingCat.of A) ⟶ FlagScheme R n)
    (hf : f ≫ toSpec R n = Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    ∃ P : CoordinateFlag A n, ofRingFlag R P = f :=
  ⟨(pointEquiv R n A).symm ⟨f, hf⟩,
    congrArg Subtype.val ((pointEquiv R n A).apply_symm_apply ⟨f, hf⟩)⟩

/-- Two morphisms into `Flₙ` are equal when their projections to all Grassmannians agree. -/
theorem hom_ext_of_steps {X : Scheme.{u}} (f g : X ⟶ FlagScheme R n)
    (h : ∀ j, f ≫ selectedFlagChartSchemeStep R n j = g ≫ selectedFlagChartSchemeStep R n j) :
    f = g :=
  selectedFlagMorphism_eq_of_projections_eq R f g h

/-- Classifying points are natural in the ring: restricting the point of `P` along `A → B`
classifies the extension of scalars of `P`. -/
@[reassoc] theorem ofRingFlag_baseChange {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] (P : CoordinateFlag A n) :
    Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ ofRingFlag R P =
      ofRingFlag R (coordinateRingFlagBaseChange (B := B) P) := by
  apply hom_ext_of_steps
  intro j
  rw [Category.assoc]
  unfold ofRingFlag
  rw [simultaneousFlagRelativeMorphism_step, simultaneousFlagRelativeMorphism_step,
    selectedQuotientMorphism_baseChange, coordinateRingFlagBaseChange_step]

/-! ### The standard flag -/

variable (n) in
/-- The standard flag `Vⱼ = span(e₁, …, eⱼ)` of `Aⁿ`. -/
def standardRingFlag (A : Type u) [CommRing A] : CoordinateFlag A n :=
  RingFlag.ofBasis (Pi.basisFun A (Fin n))

theorem standardRingFlag_step (A : Type u) [CommRing A] (j : Fin (n + 1)) :
    ((standardRingFlag n A).step j).toSubmodule =
      Submodule.span A (Pi.basisFun A (Fin n) '' {i | i.val < j.val}) := rfl

theorem standardRingFlag_baseChange (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    coordinateRingFlagBaseChange (B := B) (standardRingFlag n A) = standardRingFlag n B := by
  unfold standardRingFlag
  rw [coordinateRingFlagBaseChange_ofBasis]
  congr 1
  apply Module.Basis.eq_of_apply_eq
  intro i
  funext j
  rw [coordinateBasisBaseChange_apply, Pi.basisFun_apply, Pi.basisFun_apply]
  rcases eq_or_ne j i with rfl | h
  · simp
  · simp [h]

variable (R n) in
/-- The `R`-point of `Flₙ` given by the standard flag. -/
def standardFlag : Spec (CommRingCat.of R) ⟶ FlagScheme R n :=
  ofRingFlag R (standardRingFlag n R)

@[reassoc (attr := simp)] theorem standardFlag_toSpec : standardFlag R n ≫ toSpec R n = 𝟙 _ := by
  rw [standardFlag, ofRingFlag_toSpec, Algebra.algebraMap_self, CommRingCat.ofHom_id,
    Spec.map_id]

/-- The standard flag restricted to an `R`-algebra `A` is the standard flag of `Aⁿ`. -/
theorem spec_map_standardFlag (A : Type u) [CommRing A] [Algebra R A] :
    Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ standardFlag R n =
      ofRingFlag R (standardRingFlag n A) := by
  rw [standardFlag, ofRingFlag_baseChange, standardRingFlag_baseChange]

/-! ### Flags of locally free quotients over arbitrary schemes -/

variable (R n) in
/-- The universal complete flag of locally free quotients of `𝒪ⁿ` on `Flₙ`. -/
abbrev universalFamily : QuotientFlagFamily (FlagScheme R n) n :=
  selectedFlagUniversalFamily R n

/-- The morphism classifying a complete flag of locally free quotients of `𝒪ₓⁿ` on an
`R`-scheme `X`. -/
def classify {X : Scheme.{u}} (b : X ⟶ Spec (CommRingCat.of R)) (F : QuotientFlagFamily X n) :
    X ⟶ FlagScheme R n :=
  globalQuotientFlagMorphism R b F

@[reassoc (attr := simp)] theorem classify_toSpec {X : Scheme.{u}}
    (b : X ⟶ Spec (CommRingCat.of R)) (F : QuotientFlagFamily X n) :
    classify b F ≫ toSpec R n = b :=
  globalQuotientFlagMorphism_toSpec R b F

/-- Representability of `Flₙ`: every complete flag of locally free quotients of `𝒪ₓⁿ` over an
`R`-scheme `X` is the pullback of the universal one along a unique morphism over `Spec R`. -/
theorem existsUnique_classify {X : Scheme.{u}} (b : X ⟶ Spec (CommRingCat.of R))
    (F : QuotientFlagFamily X n) :
    ∃! f : {f : X ⟶ FlagScheme R n // f ≫ toSpec R n = b},
      ∃ e : ∀ j, (Scheme.Modules.pullback f.val).obj (selectedFlagUniversalTarget R n j) ≅
          F.target j,
        ∀ j, coordinatePullbackQuotient f.val (selectedFlagUniversalQuotient R n j) ≫
          (e j).hom = F.quotient j :=
  globalQuotientFlagUniversal_existsUnique R b F

theorem comp_classify {X Y : Scheme.{u}} (g : Y ⟶ X) (b : X ⟶ Spec (CommRingCat.of R))
    (F : QuotientFlagFamily X n) :
    g ≫ classify b F = classify (g ≫ b) (F.pullback g) :=
  globalQuotientFlagMorphism_pullback R b F g

end FlagScheme

end FlagVarieties
