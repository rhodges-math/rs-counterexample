import Schubert.FlagVarieties.Foundations.Schemes.PullbackQuotientTransport

/-!
# Original-source compatibility on the principal presentation cover

The universal quotient comparison carries the pulled-back labelled
ambient quotient to the localized ambient quotient, for every presentation
cover of every finite-projective coordinate quotient.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {n d : ℕ} {P : Module.Grassmannian A (Fin n → A) d}

set_option maxHeartbeats 400000 in
theorem SelectedQuotientCover.universalPullbackIso_source
    (D : SelectedQuotientCover R A P) (i : D.index) :
    coordinatePullbackQuotient (D.schemeCover.f i)
      (selectedUniversalAffinePullbackQuotient R A P) ≫
      (D.universalPullbackIso i).hom =
    coordinateQuotientSheafMap (CommRingCat.of (Localization.Away (D.element i)))
      (coordinateGrassmannianBaseChange (Localization.Away (D.element i)) P) := by
  unfold selectedUniversalAffinePullbackQuotient SelectedQuotientCover.universalPullbackIso
  exact coordinatePullbackQuotient_transport (D.schemeCover.f i)
    (selectedQuotientMorphism R P) (D.ι_selectedQuotientMorphism i)
    (selectedUniversalQuotient R n d)
    (selectedUniversalAffinePresentedIso R
      (CommRingCat.of (Localization.Away (D.element i))) (D.selection i) (D.evaluation i)
      (coordinateGrassmannianBaseChange (Localization.Away (D.element i)) P) (D.represents i))
    (coordinateQuotientSheafMap (CommRingCat.of (Localization.Away (D.element i)))
      (coordinateGrassmannianBaseChange (Localization.Away (D.element i)) P))
    (selectedUniversalAffinePresentedIso_source R
      (CommRingCat.of (Localization.Away (D.element i))) (D.selection i) (D.evaluation i)
      (coordinateGrassmannianBaseChange (Localization.Away (D.element i)) P) (D.represents i))

end FlagVarieties.Foundations.QuotientCharts
