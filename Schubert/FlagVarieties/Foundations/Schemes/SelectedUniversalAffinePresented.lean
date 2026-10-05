import Schubert.FlagVarieties.Foundations.Schemes.SelectedUniversalAffineChart
import Schubert.FlagVarieties.Foundations.Schemes.SelectedQuotientMorphismPresentation

/-!
# Associated-quotient comparison for presented affine families

A selected presentation identifies its free target with the
ambient module quotient. Applying tilde and the already-proved geometric
pullback frame gives a source-preserving isomorphism of sheaves.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- The associated sheaf of the original coordinate quotient module. -/
abbrev coordinateQuotientSheaf (A : CommRingCat.{u}) {n d : ℕ}
    (P : Module.Grassmannian A (Fin n → A) d) : (Spec A).Modules :=
  tilde (ModuleCat.of A ((Fin n → A) ⧸ P.toSubmodule))

/-- The original module quotient map, viewed as a map of labelled free sheaves. -/
def coordinateQuotientSheafMap (A : CommRingCat.{u}) {n d : ℕ}
    (P : Module.Grassmannian A (Fin n → A) d) :
    coordinateFreeSheaf (Spec A) n ⟶ coordinateQuotientSheaf A P :=
  (coordinateTildeFreeIso A n).inv ≫ tilde.map (ModuleCat.ofHom P.toSubmodule.mkQ)

variable (R : Type u) [CommRing R] (A : CommRingCat.{u}) [Algebra R A]
  {n d : ℕ} (a : Fin d ↪ Fin n)
  (f : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A)
  (P : Module.Grassmannian A (Fin n → A) d)
  (he : selectedChartPoint R a f = P)

/-- A selected presentation retains the original quotient module. -/
def selectedUniversalPresentedQuotientEquiv : (Fin d → A) ≃ₗ[A] ((Fin n → A) ⧸ P.toSubmodule) :=
  quotientPresentationEquiv (selectedPresentationMap R a f) P.toSubmodule.mkQ
    (selectedPresentationMap_surjective R a f) P.toSubmodule.mkQ_surjective
    (by rw [selectedPresentationMap_ker, Submodule.ker_mkQ, he])

/-- The target identification preserves every original ambient quotient vector. -/
theorem selectedUniversalPresentedQuotientEquiv_comp :
    (selectedUniversalPresentedQuotientEquiv R A a f P he).toLinearMap.comp
      (selectedPresentationMap R a f) = P.toSubmodule.mkQ :=
  quotientPresentationEquiv_comp _ _ _ _ _

/-- The associated-sheaf target identification. -/
def selectedPresentationQuotientSheafIso :
    coordinateFreeSheaf (Spec A) d ≅ coordinateQuotientSheaf A P :=
  (coordinateTildeFreeIso A d).symm ≪≫
    (tilde.functor A).mapIso (selectedUniversalPresentedQuotientEquiv R A a f P he).toModuleIso

/-- This associated-sheaf isomorphism preserves the original quotient morphism. -/
@[reassoc]
theorem selectedPresentationQuotientSheafIso_source :
    selectedPresentationSheafMap R A a f ≫
      (selectedPresentationQuotientSheafIso R A a f P he).hom =
      coordinateQuotientSheafMap A P := by
  simp only [selectedPresentationSheafMap, selectedPresentationQuotientSheafIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc, Iso.hom_inv_id_assoc]
  change (coordinateTildeFreeIso A n).inv ≫
    tilde.map (ModuleCat.ofHom (selectedPresentationMap R a f)) ≫
    tilde.map
      (ModuleCat.ofHom (selectedUniversalPresentedQuotientEquiv R A a f P he).toLinearMap) = _
  rw [← tilde.map_comp, ← ModuleCat.ofHom_comp, selectedUniversalPresentedQuotientEquiv_comp]
  rfl

/-- Pullback to a presented affine family is its associated quotient sheaf. -/
def selectedUniversalAffinePresentedIso :
    (Scheme.Modules.pullback (selectedChartPointMap R a f)).obj
      (selectedUniversalQuotientSheaf R n d) ≅ coordinateQuotientSheaf A P :=
  selectedUniversalAffineChartFrame R a A f ≪≫
    selectedPresentationQuotientSheafIso R A a f P he

/-- The affine-family comparison preserves the original quotient map. -/
@[reassoc]
theorem selectedUniversalAffinePresentedIso_source :
    coordinatePullbackQuotient (selectedChartPointMap R a f)
      (selectedUniversalQuotient R n d) ≫
        (selectedUniversalAffinePresentedIso R A a f P he).hom =
      coordinateQuotientSheafMap A P := by
  simp only [selectedUniversalAffinePresentedIso, Iso.trans_hom]
  rw [← Category.assoc, selectedUniversalAffineChartFrame_source,
    selectedPresentationQuotientSheafIso_source]

/-- The same comparison along the intrinsic quotient morphism whenever this
global selected presentation exists. -/
def selectedUniversalPresentedMorphismIso :
    (Scheme.Modules.pullback (selectedQuotientMorphism R P)).obj
      (selectedUniversalQuotientSheaf R n d) ≅ coordinateQuotientSheaf A P :=
  (Scheme.Modules.pullbackCongr (selectedQuotientMorphism_eq_pointMap a f he.symm)).app
    (selectedUniversalQuotientSheaf R n d) ≪≫
      selectedUniversalAffinePresentedIso R A a f P he

@[reassoc]
theorem selectedUniversalPresentedMorphismIso_source :
    coordinatePullbackQuotient (selectedQuotientMorphism R P)
      (selectedUniversalQuotient R n d) ≫
        (selectedUniversalPresentedMorphismIso R A a f P he).hom =
      coordinateQuotientSheafMap A P := by
  simp only [selectedUniversalPresentedMorphismIso, Iso.trans_hom, Iso.app_hom]
  rw [coordinatePullbackQuotient_congr_assoc, selectedUniversalAffinePresentedIso_source]

end FlagVarieties.Foundations.QuotientCharts
