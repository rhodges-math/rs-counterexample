import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedUniversalAffinePresented

/-!
# Pullback comparisons on the derived principal presentation cover

Every finite-projective coordinate quotient supplies its own principal
presentation cover. On that cover the pullback of the constructed global
quotient is its localized associated quotient, preserving source labels.
The global identification with the associated sheaf of the original
quotient is `Schemes/SelectedUniversalAffineQuotientComparison.lean`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  {n d : ℕ} (P : Module.Grassmannian A (Fin n → A) d)

/-- The global universal target pulled back along the intrinsic affine quotient morphism. -/
abbrev selectedUniversalAffinePullback : (Spec (CommRingCat.of A)).Modules :=
  (Scheme.Modules.pullback (selectedQuotientMorphism R P)).obj
    (selectedUniversalQuotientSheaf R n d)

/-- Its epimorphic quotient map, with the original labelled free source. -/
def selectedUniversalAffinePullbackQuotient :
    coordinateFreeSheaf (Spec (CommRingCat.of A)) n ⟶ selectedUniversalAffinePullback R A P :=
  coordinatePullbackQuotient (selectedQuotientMorphism R P) (selectedUniversalQuotient R n d)

instance selectedUniversalAffinePullbackQuotient_epi :
    Epi (selectedUniversalAffinePullbackQuotient R A P) := by
  unfold selectedUniversalAffinePullbackQuotient
  infer_instance

variable {R A P}

/-- Local associated-quotient comparison for any presentation cover. -/
def SelectedQuotientCover.universalPullbackIso (D : SelectedQuotientCover R A P) (i : D.index) :
    (Scheme.Modules.pullback (D.schemeCover.f i)).obj (selectedUniversalAffinePullback R A P) ≅
      coordinateQuotientSheaf (CommRingCat.of (Localization.Away (D.element i)))
        (coordinateGrassmannianBaseChange (Localization.Away (D.element i)) P) :=
  (Scheme.Modules.pullbackComp (D.schemeCover.f i) (selectedQuotientMorphism R P)).app
    (selectedUniversalQuotientSheaf R n d) ≪≫
  (Scheme.Modules.pullbackCongr (D.ι_selectedQuotientMorphism i)).app
    (selectedUniversalQuotientSheaf R n d) ≪≫
  selectedUniversalAffinePresentedIso R
    (CommRingCat.of (Localization.Away (D.element i))) (D.selection i) (D.evaluation i)
    (coordinateGrassmannianBaseChange (Localization.Away (D.element i)) P) (D.represents i)

theorem coordinatePullbackQuotient_comp_hom {X Y Z : Scheme.{u}} {n : ℕ}
    (f : X ⟶ Y) (g : Y ⟶ Z) {M : Z.Modules}
    (q : coordinateFreeSheaf Z n ⟶ M) :
    coordinatePullbackQuotient f (coordinatePullbackQuotient g q) ≫
      (Scheme.Modules.pullbackComp f g).hom.app M =
      coordinatePullbackQuotient (f ≫ g) q := by
  rw [← coordinatePullbackQuotient_comp]
  simp

end FlagVarieties.Foundations.QuotientCharts
