import RSCounterexample.FlagVarieties.Foundations.Schemes.QuotientPairCoordinates
import RSCounterexample.FlagVarieties.Foundations.Schemes.ProjectiveLineGluing

/-!
# Local projective coordinates from scalar-extended quotient frames

This is an algebraic bridge on a source scheme. A single surjection
from the ordered free pair over its global-section ring is extended to each
covering open. Frames of these tensor modules supply the coordinates;
their coprimality and common-unit overlap relations are proved, not inputs.
The resulting morphism to the projective line is
`Schemes/QuotientPairScheme.lean`.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientPair

open AlgebraicGeometry CategoryTheory TensorProduct

universe u v

variable {X : Scheme.{u}}

/-- The ring of functions on the open subscheme `U`. -/
abbrev RingOn (U : X.Opens) := Γ(U.toScheme, ⊤)

/-- The scalar structure is induced by the open inclusion. -/
@[instance_reducible] def openAlgebra (U : X.Opens) : Algebra Γ(X, ⊤) (RingOn U) :=
  U.ι.appTop.hom.toAlgebra

attribute [local instance] openAlgebra

variable {Q : Type u} [AddCommGroup Q] [Module Γ(X, ⊤) Q]

/-- The base change of the `Γ(X, ⊤)`-module `Q` to the open subscheme `U`. -/
abbrev ModuleOn (U : X.Opens) := RingOn U ⊗[Γ(X, ⊤)] Q

theorem open_algebraMap_comp {U V : X.Opens} (h : V ≤ U) :
    (X.homOfLE h).appTop.hom.comp (algebraMap Γ(X, ⊤) (RingOn U)) =
      algebraMap Γ(X, ⊤) (RingOn V) := by
  change (X.homOfLE h).appTop.hom.comp U.ι.appTop.hom = V.ι.appTop.hom
  rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, Scheme.homOfLE_ι]

/-- A local frame extends canonically to every smaller open. -/
def restrictFrame {U V : X.Opens} (h : V ≤ U)
    (frame : ModuleOn (Q := Q) U ≃ₗ[RingOn U] RingOn U) :
    ModuleOn (Q := Q) V ≃ₗ[RingOn V] RingOn V := by
  letI : Algebra (RingOn U) (RingOn V) := (X.homOfLE h).appTop.hom.toAlgebra
  letI : IsScalarTower Γ(X, ⊤) (RingOn U) (RingOn V) :=
    IsScalarTower.of_algebraMap_eq' (open_algebraMap_comp h).symm
  exact extendFrame frame

@[simp] theorem restrictFrame_one_tmul {U V : X.Opens} (h : V ≤ U)
    (frame : ModuleOn (Q := Q) U ≃ₗ[RingOn U] RingOn U) (x : Q) :
    restrictFrame h frame (1 ⊗ₜ[Γ(X, ⊤)] x) =
      (X.homOfLE h).appTop (frame (1 ⊗ₜ[Γ(X, ⊤)] x)) := by
  let : Algebra (RingOn U) (RingOn V) := (X.homOfLE h).appTop.hom.toAlgebra
  let : IsScalarTower Γ(X, ⊤) (RingOn U) (RingOn V) :=
    IsScalarTower.of_algebraMap_eq' (open_algebraMap_comp h).symm
  exact extendFrame_one_tmul frame x

/-- Compatibility on overlaps is derived from the two induced frames of one tensor module. -/
theorem frames_overlap_common_unit {ι : Type v} {U : ι → X.Opens}
    (frames : ∀ i, ModuleOn (Q := Q) (U i) ≃ₗ[RingOn (U i)] RingOn (U i))
    (x y : Q) (i j : ι) :
    ∃ u : (RingOn (U i ⊓ U j))ˣ,
      (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).appTop
          (frames i (1 ⊗ₜ[Γ(X, ⊤)] x)) = (u : RingOn (U i ⊓ U j)) *
        (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).appTop
          (frames j (1 ⊗ₜ[Γ(X, ⊤)] x)) ∧
      (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).appTop
          (frames i (1 ⊗ₜ[Γ(X, ⊤)] y)) = (u : RingOn (U i ⊓ U j)) *
        (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).appTop
          (frames j (1 ⊗ₜ[Γ(X, ⊤)] y)) := by
  simpa only [restrictFrame_one_tmul] using
    quotient_frame_change_pair
      (restrictFrame (inf_le_right : U i ⊓ U j ≤ U j) (frames j))
      (restrictFrame (inf_le_left : U i ⊓ U j ≤ U i) (frames i))
      (1 ⊗ₜ[Γ(X, ⊤)] x) (1 ⊗ₜ[Γ(X, ⊤)] y)

/-- Construct every coordinate and transition field of `OpenPairData` from quotient frames. -/
def openPairData {ι : Type v} {U : ι → X.Opens}
    (q : Γ(X, ⊤) × Γ(X, ⊤) →ₗ[Γ(X, ⊤)] Q) (hq : Function.Surjective q)
    (frames : ∀ i, ModuleOn (Q := Q) (U i) ≃ₗ[RingOn (U i)] RingOn (U i)) :
    ProjectiveLine.OpenPairData U := by
  classical
  choose units hδ hε using frames_overlap_common_unit frames (q (1, 0)) (q (0, 1))
  exact {
    delta := fun i => frames i (1 ⊗ₜ[Γ(X, ⊤)] q (1, 0))
    epsilon := fun i => frames i (1 ⊗ₜ[Γ(X, ⊤)] q (0, 1))
    coprime := fun i => frame_coordinates_coprime q hq (frames i)
    transition := units
    delta_transition := hδ
    epsilon_transition := hε }

end FlagVarieties.Foundations.QuotientPair
