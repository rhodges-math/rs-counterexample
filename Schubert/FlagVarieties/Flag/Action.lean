import Schubert.FlagVarieties.Flag.Basic
import Schubert.FlagVarieties.Flag.ActionLaws

/-!
# The action of `GLₙ` on the flag scheme

* `FlagVarieties.GLOver R n`, `FlagVarieties.GLScheme R n`: Tau Ceti's general linear group
  scheme over `R`, as a group object of the slice over `Spec R`, and its underlying scheme.
* `FlagScheme.action`: the action morphism `GLₙ ×_R Flₙ ⟶ Flₙ`. On points it sends `(g, V•)` to
  `g · V• = (g V₀ ⊆ g V₁ ⊆ ⋯)` (`FlagScheme.action_point`).
* The instance `ModObj (GLOver R n) (FlagScheme.over R n)`: the action is a left action of the
  group object (unit and associativity laws in the slice category).
* `FlagScheme.orbitMap`: the orbit map `π : GLₙ ⟶ Flₙ`, `g ↦ g · E•`, of the standard flag; on
  points `π(g)` is the flag of spans of the initial columns of `g` (`orbitMap_point_step`).
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open Foundations Foundations.QuotientCharts

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

/-- Tau Ceti's general linear group scheme `GLₙ` over `R`, a group object of `Over (Spec R)`. -/
abbrev GLOver : Over (Spec (CommRingCat.of R)) :=
  (TauCeti.GeneralLinear.groupScheme R n).X

/-- The scheme underlying `GLₙ`; it is `Spec` of `TauCeti.GeneralLinear.CoordinateRing R n`. -/
abbrev GLScheme : Scheme.{u} :=
  (GLOver R n).left

/-- The `A`-valued point of `GLₙ` given by an `R`-algebra map out of the coordinate ring. -/
abbrev GLScheme.point {A : Type u} [CommRing A] [Algebra R A]
    (k : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] A) :
    Spec (CommRingCat.of A) ⟶ GLScheme R n :=
  generalLinearGroupPoint R A n k

/-- The invertible matrix of an `A`-valued point of `GLₙ`. -/
abbrev GLScheme.pointMatrix {A : Type u} [CommRing A] [Algebra R A]
    (k : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] A) : Matrix (Fin n) (Fin n) A :=
  generalLinearMatrixAt R A n k

/-- The linear automorphism of `Aⁿ` of an `A`-valued point of `GLₙ`. -/
abbrev GLScheme.pointEquiv {A : Type u} [CommRing A] [Algebra R A]
    (k : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] A) : (Fin n → A) ≃ₗ[A] (Fin n → A) :=
  (generalLinearMatrixAt R A n k).toLinearEquiv' (generalLinearMatrixAt_isUnit R A n k).invertible

namespace FlagScheme

/-- `Flₙ` as an object of the slice category over `Spec R`. -/
abbrev over : Over (Spec (CommRingCat.of R)) :=
  generalLinearFlagOver R n

/-- The action morphism `GLₙ ×_R Flₙ ⟶ Flₙ`. -/
abbrev action : pullback (GLOver R n).hom (toSpec R n) ⟶ FlagScheme R n :=
  generalLinearFlagAction R n

@[reassoc (attr := simp)] theorem action_toSpec :
    action R n ≫ toSpec R n = pullback.snd _ _ ≫ toSpec R n :=
  generalLinearFlagAction_toSpec R n

/-- The action as a morphism of the slice category. -/
abbrev overAction : GLOver R n ⊗ over R n ⟶ over R n :=
  generalLinearFlagOverAction R n

/-- The action is a left action of the group object `GLₙ`. -/
instance : ModObj (GLOver R n) (over R n) :=
  instGeneralLinearFlagModObj R n

theorem smul_left : (ModObj.smul (M := GLOver R n) (X := over R n)).left = action R n := rfl

/-- The unit law of the action, as scheme morphisms. -/
theorem action_one :
    generalLinearFlagUnitSection R n ≫ action R n = 𝟙 (FlagScheme R n) :=
  generalLinearFlagAction_unit R n

/-- The associativity law of the action, as scheme morphisms. -/
theorem action_mul :
    generalLinearFlagMultipliedAction R n = generalLinearFlagSuccessiveAction R n :=
  generalLinearFlagAction_mul R n

variable {R n}

/-- On points, the action sends `(g, V•)` to `g · V•`. -/
theorem action_point {A : Type u} [CommRing A] [Algebra R A]
    (k : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] A) (P : CoordinateFlag A n) :
    pullback.lift (GLScheme.point R n k) (ofRingFlag R P)
        ((generalLinearGroupPoint_toSpec R A n k).trans (ofRingFlag_toSpec P).symm) ≫
      action R n = ofRingFlag R (P.transport (GLScheme.pointEquiv R n k)) :=
  generalLinearFlagAction_evaluate R A n k P

variable (R n)

/-- The orbit map `π : GLₙ ⟶ Flₙ`, `g ↦ g · E•`. -/
def orbitMap : GLScheme R n ⟶ FlagScheme R n :=
  pullback.lift (𝟙 _) ((GLOver R n).hom ≫ standardFlag R n) (by simp) ≫ action R n

@[reassoc (attr := simp)] theorem orbitMap_toSpec :
    orbitMap R n ≫ toSpec R n = (GLOver R n).hom := by
  simp [orbitMap]

variable {R n}

/-- On points, `π(g) = g · E•`. -/
theorem orbitMap_point {A : Type u} [CommRing A] [Algebra R A]
    (k : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] A) :
    GLScheme.point R n k ≫ orbitMap R n =
      ofRingFlag R ((standardRingFlag n A).transport (GLScheme.pointEquiv R n k)) := by
  rw [← action_point]
  unfold orbitMap
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc,
      generalLinearGroupPoint_toSpec, spec_map_standardFlag]

/-- The steps of `π(g)` are the spans of the initial columns of `g`. -/
theorem orbitMap_point_step {A : Type u} [CommRing A] [Algebra R A]
    (k : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] A) (j : Fin (n + 1)) :
    ((((standardRingFlag n A).transport (GLScheme.pointEquiv R n k)).step j).toSubmodule) =
      Submodule.span A ((fun i => (GLScheme.pointMatrix R n k).col i) '' {i | i.val < j.val}) := by
  rw [RingFlag.transport_step, standardRingFlag_step, Submodule.map_span, Set.image_image]
  congr 1
  apply Set.image_congr
  intro i _
  simp [Matrix.toLinearEquiv'_apply]

end FlagScheme

end FlagVarieties
