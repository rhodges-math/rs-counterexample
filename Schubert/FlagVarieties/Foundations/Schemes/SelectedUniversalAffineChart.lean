import Schubert.FlagVarieties.Foundations.Schemes.SelectedUniversalPullbackFrames

/-!
# The universal quotient pulled back to every affine chart family

An arbitrary polynomial evaluation defines a morphism from its
coefficient spectrum. Pulling back the constructed global quotient gives
its original selected presentation, with canonical source labels retained.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : Type u) [CommRing R] {n d : ℕ} (a : Fin d ↪ Fin n)

/-- The existing range-open frame, viewed through pullback. -/
def selectedUniversalOpenPullbackFrame :
    (Scheme.Modules.pullback (selectedUniversalOpen R n d a).ι).obj
      (selectedUniversalQuotientSheaf R n d) ≅
      coordinateFreeSheaf (selectedUniversalOpen R n d a).toScheme d :=
  ((Scheme.Modules.restrictFunctorIsoPullback (selectedUniversalOpen R n d a).ι).app
    (selectedUniversalQuotientSheaf R n d)).symm ≪≫ selectedUniversalQuotientFrame R n d a

/-- The pullback frame retains the original quotient formula on the range open. -/
theorem selectedUniversalOpenPullbackFrame_source :
    coordinatePullbackQuotient (selectedUniversalOpen R n d a).ι
      (selectedUniversalQuotient R n d) ≫ (selectedUniversalOpenPullbackFrame R a).hom =
    selectedUniversalNormalizedQuotient R a := by
  change coordinatePullbackQuotient (selectedUniversalOpen R n d a).ι
      (selectedUniversalQuotient R n d) ≫
    (Scheme.Modules.restrictFunctorIsoPullback (selectedUniversalOpen R n d a).ι).inv.app
      (selectedUniversalQuotientSheaf R n d) ≫ (selectedUniversalQuotientFrame R n d a).hom = _
  rw [coordinatePullbackQuotient_restrict_assoc]
  exact selectedUniversalQuotient_chart_formula R n d a

/-- The original chart inclusion factors through its range open. -/
theorem selectedUniversalChart_factor :
    (selectedUniversalOpenIso R n d a).hom ≫ (selectedUniversalOpen R n d a).ι =
      selectedChartSchemeChart R n d a :=
  Scheme.Hom.isoOpensRange_hom_ι (selectedChartSchemeChart R n d a)

/-- Pullback of the global target to the original polynomial chart. -/
def selectedUniversalChartPullbackFrame :
    (Scheme.Modules.pullback (selectedChartSchemeChart R n d a)).obj
      (selectedUniversalQuotientSheaf R n d) ≅
      coordinateFreeSheaf (Spec (CommRingCat.of (MvPolynomial (Fin d × Fin (n - d)) R))) d :=
  (Scheme.Modules.pullbackCongr (selectedUniversalChart_factor R a).symm).app
    (selectedUniversalQuotientSheaf R n d) ≪≫
      coordinatePullbackFrameComp (selectedUniversalOpenIso R n d a).hom
        (selectedUniversalOpen R n d a).ι (selectedUniversalQuotientSheaf R n d)
        (selectedUniversalOpenPullbackFrame R a)

/-- The pulled-back quotient is the identity-evaluated matrix quotient. -/
theorem selectedUniversalChartPullbackFrame_source :
    coordinatePullbackQuotient (selectedChartSchemeChart R n d a)
      (selectedUniversalQuotient R n d) ≫ (selectedUniversalChartPullbackFrame R a).hom =
    selectedPresentationSheafMap R
      (CommRingCat.of (MvPolynomial (Fin d × Fin (n - d)) R)) a (AlgHom.id R _) := by
  unfold selectedUniversalChartPullbackFrame
  simp only [Iso.trans_hom, Iso.app_hom]
  rw [coordinatePullbackQuotient_congr_assoc,
    coordinatePullbackFrameComp_source _ _ _ _ _ (selectedUniversalOpenPullbackFrame_source R a)]
  rw [← coordinateRestrictMap_eq_pullback]
  unfold selectedUniversalNormalizedQuotient
  rw [coordinateRestrictMap_comp_scheme]
  simp only [Iso.hom_inv_id, coordinateRestrictMap_id]

variable (A : CommRingCat.{u}) [Algebra R A]
  (f : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A)

/-- The universal target on every affine selected-chart family. -/
def selectedUniversalAffineChartFrame :
    (Scheme.Modules.pullback (selectedChartPointMap R a f)).obj
      (selectedUniversalQuotientSheaf R n d) ≅ coordinateFreeSheaf (Spec A) d :=
  coordinatePullbackFrameComp (Spec.map (CommRingCat.ofHom f.toRingHom))
    (selectedChartSchemeChart R n d a) (selectedUniversalQuotientSheaf R n d)
    (selectedUniversalChartPullbackFrame R a)

/-- For every coefficient algebra, geometric pullback gives exactly its
original selected quotient sheaf map, with no flatness or basis hypothesis. -/
theorem selectedUniversalAffineChartFrame_source :
    coordinatePullbackQuotient (selectedChartPointMap R a f)
      (selectedUniversalQuotient R n d) ≫ (selectedUniversalAffineChartFrame R a A f).hom =
    selectedPresentationSheafMap R A a f := by
  change coordinatePullbackQuotient
    (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ selectedChartSchemeChart R n d a)
      (selectedUniversalQuotient R n d) ≫
    (coordinatePullbackFrameComp _ _ _ (selectedUniversalChartPullbackFrame R a)).hom = _
  rw [coordinatePullbackFrameComp_source _ _ _ _ _ (selectedUniversalChartPullbackFrame_source R a)]
  change (coordinatePullbackIso _ n).inv ≫ _ ≫ (coordinatePullbackIso _ d).hom = _
  simpa only [AlgHom.comp_id] using selectedPresentationSheafMap_pullback_conjugate R
    (CommRingCat.of (MvPolynomial (Fin d × Fin (n - d)) R)) A a (AlgHom.id R _) f

end FlagVarieties.Foundations.QuotientCharts
