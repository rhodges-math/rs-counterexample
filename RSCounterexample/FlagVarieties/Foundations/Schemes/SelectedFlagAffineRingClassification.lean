import RSCounterexample.FlagVarieties.Foundations.Schemes.AffineQuotientFlagClassification
import RSCounterexample.FlagVarieties.Foundations.Schemes.AffineLocallyFreeCoordinateClassification

/-!
# Affine flag morphisms and original ring-valued flags

Pulling back the universal quotient family and taking its original
affine coordinate kernels is inverse to the derived simultaneous-cover
classifying morphism. Both inverse laws retain every original quotient map.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory

universe u

variable (R : Type u) [CommRing R] (A : CommRingCat.{u}) [Algebra R A]
  (n : ℕ)

/-- Scheme morphisms over the fixed coefficient map `R → A`. -/
abbrev selectedFlagAffineOverBase :=
  {f : Spec A ⟶ selectedFlagChartScheme R n //
    f ≫ selectedFlagChartSchemeToSpec R n =
      Spec.map (CommRingCat.ofHom (algebraMap R A))}

/-- Recover a ring flag using the pulled-back universal quotient
family, its original sheaf arrows, and their affine coordinate kernels. -/
def selectedFlagRingOfAffine (f : selectedFlagAffineOverBase R A n) :
    RingFlag A (Fin n → A) n :=
  ((selectedFlagUniversalFamily R n).pullback f.val).toRingFlag A

/-- The original ring flag gives its proved relative classifying morphism. -/
def selectedFlagAffineOfRing (P : RingFlag A (Fin n → A) n) :
    selectedFlagAffineOverBase R A n :=
  ⟨simultaneousFlagRelativeMorphism R P,
    simultaneousFlagRelativeMorphism_toSpec R P⟩

/-- Recovering the flag after classifying it returns every original
Grassmannian quotient step and hence the original RingFlag. -/
theorem selectedFlagRingOfAffine_ofRing (P : RingFlag A (Fin n → A) n) :
    selectedFlagRingOfAffine R A n (selectedFlagAffineOfRing R A n P) = P := by
  let m := simultaneousFlagRelativeMorphism R P
  let U : QuotientFlagFamily (Spec A) n := (selectedFlagUniversalFamily R n).pullback m
  apply RingFlag.ext
  intro j
  letI : Epi (coordinatePullbackQuotient m (selectedFlagUniversalQuotient R n j)) :=
    inferInstance
  let c := selectedFlagAffineStepIso R A P m
    (simultaneousFlagRelativeMorphism_step R P) j
  have hs : coordinateQuotientSheafMap A (P.step j) ≫ c.inv =
      coordinatePullbackQuotient m (selectedFlagUniversalQuotient R n j) := by
    have h := selectedFlagAffineStepIso_source R A P m
      (simultaneousFlagRelativeMorphism_step R P) j
    calc
      coordinateQuotientSheafMap A (P.step j) ≫ c.inv =
          (coordinatePullbackQuotient m (selectedFlagUniversalQuotient R n j) ≫ c.hom) ≫
            c.inv := congrArg (fun t => t ≫ c.inv) h.symm
      _ = coordinatePullbackQuotient m (selectedFlagUniversalQuotient R n j) := by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hP := affineLocallyFreeGrassmannian_unique A
    (coordinatePullbackQuotient m (selectedFlagUniversalQuotient R n j))
    (n-j.val) (U.local_frames j) (P.step j) c.symm hs
  exact congrArg Module.Grassmannian.toSubmodule hP.symm

/-- Classifying the pulled-back universal family recovers the original
over-base scheme morphism, including its structure-sheaf map. -/
theorem selectedFlagAffineOfRing_ringOfAffine
    (f : selectedFlagAffineOverBase R A n) :
    selectedFlagAffineOfRing R A n (selectedFlagRingOfAffine R A n f) = f := by
  apply Subtype.ext
  let U : QuotientFlagFamily (Spec A) n := (selectedFlagUniversalFamily R n).pullback f.val
  have h := affineQuotientFlagMorphism_unique R A U f.val f.property
    (fun j => Iso.refl ((Scheme.Modules.pullback f.val).obj (selectedFlagUniversalTarget R n j)))
    (by intro j; rfl)
  exact h.symm

/-- Affine points of the glued flag scheme over `R` are precisely
the original finite-projective quotient flags over `A`. -/
def selectedFlagAffineRingEquiv :
    RingFlag A (Fin n → A) n ≃ selectedFlagAffineOverBase R A n where
  toFun := selectedFlagAffineOfRing R A n
  invFun := selectedFlagRingOfAffine R A n
  left_inv := selectedFlagRingOfAffine_ofRing R A n
  right_inv := selectedFlagAffineOfRing_ringOfAffine R A n

end FlagVarieties.Foundations.QuotientCharts
