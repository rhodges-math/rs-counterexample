import RSCounterexample.FlagVarieties.Foundations.Schemes.CoordinateQuotientCoverDescent
import RSCounterexample.FlagVarieties.Foundations.Schemes.AffineCoordinateQuotientBaseChangeCoordinateSource

/-!
# Comparing the two affine quotient sheaves on the derived cover

The universal quotient pulled back along the intrinsic quotient morphism
and the associated sheaf of the original module quotient have
source-preserving isomorphic pullbacks on the derived presentation cover.
Descent then identifies the quotient sheaves globally, preserving
the original labelled source. No global basis or presentation cover is
part of the input, and the result is independent of the derived cover.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {n d : ℕ} {P : Module.Grassmannian A (Fin n → A) d}

/-- Both quotient sheaves are compared on each original localization domain. -/
def SelectedQuotientCover.associatedPullbackIso (D : SelectedQuotientCover R A P)
    (i : D.index) :
    (Scheme.Modules.pullback (D.schemeCover.f i)).obj (selectedUniversalAffinePullback R A P) ≅
      (Scheme.Modules.pullback (D.schemeCover.f i)).obj
        (coordinateQuotientSheaf (CommRingCat.of A) P) :=
  D.universalPullbackIso i ≪≫
    (coordinateQuotientSheafPullbackIso A (Localization.Away (D.element i)) P).symm

@[reassoc]
theorem SelectedQuotientCover.associatedPullbackIso_source
    (D : SelectedQuotientCover R A P) (i : D.index) :
    coordinatePullbackQuotient (D.schemeCover.f i)
        (selectedUniversalAffinePullbackQuotient R A P) ≫
      (D.associatedPullbackIso i).hom =
    coordinatePullbackQuotient (D.schemeCover.f i)
      (coordinateQuotientSheafMap (CommRingCat.of A) P) := by
  apply (cancel_mono (coordinateQuotientSheafPullbackIso A
    (Localization.Away (D.element i)) P).hom).mp
  simp only [SelectedQuotientCover.associatedPullbackIso, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [D.universalPullbackIso_source i]
  exact (coordinateQuotientSheafPullbackIso_coordinate_source A
    (Localization.Away (D.element i)) P).symm

/-- Descend the source-preserving comparisons over any derived presentation cover. -/
def SelectedQuotientCover.associatedQuotientIso (D : SelectedQuotientCover R A P) :
    selectedUniversalAffinePullback R A P ≅ coordinateQuotientSheaf (CommRingCat.of A) P :=
  coordinateQuotientIsoOfCover D.schemeCover
    (selectedUniversalAffinePullbackQuotient R A P)
    (coordinateQuotientSheafMap (CommRingCat.of A) P)
    D.associatedPullbackIso D.associatedPullbackIso_source

@[reassoc]
theorem SelectedQuotientCover.associatedQuotientIso_source (D : SelectedQuotientCover R A P) :
    selectedUniversalAffinePullbackQuotient R A P ≫ D.associatedQuotientIso.hom =
      coordinateQuotientSheafMap (CommRingCat.of A) P :=
  coordinateQuotientIsoOfCover_source D.schemeCover
    (selectedUniversalAffinePullbackQuotient R A P)
    (coordinateQuotientSheafMap (CommRingCat.of A) P)
    D.associatedPullbackIso D.associatedPullbackIso_source

variable (R A P)

/-- Pulling back the universal quotient along a quotient's intrinsic
classifying map recovers its associated quotient sheaf. -/
def selectedUniversalAffineQuotientIso :
    selectedUniversalAffinePullback R A P ≅ coordinateQuotientSheaf (CommRingCat.of A) P :=
  (selectedQuotientCover R A P).associatedQuotientIso

@[reassoc]
theorem selectedUniversalAffineQuotientIso_source :
    selectedUniversalAffinePullbackQuotient R A P ≫
      (selectedUniversalAffineQuotientIso R A P).hom =
    coordinateQuotientSheafMap (CommRingCat.of A) P :=
  (selectedQuotientCover R A P).associatedQuotientIso_source

/-- Every presentation cover yields the same source-preserving global comparison. -/
theorem SelectedQuotientCover.associatedQuotientIso_eq (D : SelectedQuotientCover R A P) :
    D.associatedQuotientIso = selectedUniversalAffineQuotientIso R A P :=
  ModuleSheafGluing.quotientIso_unique
    (selectedUniversalAffinePullbackQuotient R A P)
    (coordinateQuotientSheafMap (CommRingCat.of A) P)
    _ _ D.associatedQuotientIso_source (selectedUniversalAffineQuotientIso_source R A P)

end FlagVarieties.Foundations.QuotientCharts
