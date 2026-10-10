import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedMatrixAction
import RSCounterexample.FlagVarieties.Foundations.Schemes.ConstantMatrixSheafAffine
import RSCounterexample.FlagVarieties.Foundations.Schemes.ConstantMatrixAffineQuotient
import RSCounterexample.FlagVarieties.Foundations.Schemes.AffineCoordinateSheafRecovery
import RSCounterexample.FlagVarieties.Foundations.Flags.GrassmannianTransport
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedProjectiveField

/-! The constant-matrix Grassmannian scheme morphism on affine points. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory ModuleSheafGluing
universe u

private theorem global_classifier_eq_affine (R : Type u) [CommRing R]
    (A : CommRingCat.{u}) [Algebra R A] {n : ℕ} {M : (Spec A).Modules}
    (q : coordinateFreeSheaf (Spec A) n ⟶ M) [Epi q] (d : ℕ)
    (hfree : ∀ p : Spec A, ∃ U : (Spec A).Opens, p ∈ U ∧
      Nonempty (M.over U ≅
        SheafOfModules.free (R := (Spec A).ringCatSheaf.over U) (CoordinateIndex.{u} d))) :
    globalLocallyFreeQuotientMorphism R
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) q d hfree =
    affineLocallyFreeQuotientMorphism R A q d hfree := by
  exact affineLocallyFreeQuotientMorphism_unique R A q d hfree
    (globalLocallyFreeQuotientMorphism R
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) q d hfree)
    (globalLocallyFreeQuotientMorphism_toSpec R _ q d hfree)
    (globalLocallyFreeUniversalIso R _ q d hfree)
    (globalLocallyFreeUniversalIso_source R _ q d hfree)

private theorem affineCoordinateQuotientMap_targetIso_ker
    (A : CommRingCat.{u}) {n : ℕ} {M N : (Spec A).Modules}
    (q : coordinateFreeSheaf (Spec A) n ⟶ M) (e : M ≅ N) :
    LinearMap.ker (affineCoordinateQuotientMap A (q ≫ e.hom)) =
      LinearMap.ker (affineCoordinateQuotientMap A q) := by
  have hm : affineCoordinateQuotientMap A (q ≫ e.hom) =
      (moduleSpecΓFunctor.map e.hom).hom.comp (affineCoordinateQuotientMap A q) := by
    apply LinearMap.ext
    intro x
    change (moduleSpecΓFunctor.map (q ≫ e.hom)).hom
      ((coordinateFreeGlobalIso A n).hom.hom x) = _
    rw [Functor.map_comp]
    rfl
  rw [hm]
  apply Submodule.ext
  intro x
  have hi : Function.Injective (moduleSpecΓFunctor.map e.hom).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  simp only [LinearMap.mem_ker, LinearMap.comp_apply]
  constructor
  · intro hx
    apply hi
    simpa only [map_zero] using hx
  · intro hx
    rw [hx, map_zero]

theorem affineLocallyFreeGrassmannian_constantMatrix
    (A : CommRingCat.{u}) {n : ℕ} {M : (Spec A).Modules}
    (q : coordinateFreeSheaf (Spec A) n ⟶ M) [Epi q] (d : ℕ)
    (hfree : ∀ p : Spec A, ∃ U : (Spec A).Opens, p ∈ U ∧
      Nonempty (M.over U ≅
        SheafOfModules.free (R := (Spec A).ringCatSheaf.over U) (CoordinateIndex.{u} d)))
    (L : Matrix (Fin n) (Fin n) A) (hL : IsUnit L) :
    affineLocallyFreeGrassmannian A
        ((constantMatrixSpecIso A L hL).inv ≫ q) d hfree =
      grassmannianTransport (affineLocallyFreeGrassmannian A q d hfree)
        (L.toLinearEquiv' hL.invertible) := by
  apply Module.Grassmannian.ext
  change LinearMap.ker (affineCoordinateQuotientMap A
      ((constantMatrixSpecIso A L hL).inv ≫ q)) =
    Submodule.map (L.toLinearEquiv' hL.invertible).toLinearMap
      (LinearMap.ker (affineCoordinateQuotientMap A q))
  exact affineCoordinateQuotientMap_constantMatrix_inv_ker A L hL q

/-- On every coefficient algebra, the scheme action transports the
original Grassmannian kernel by the entrywise specialized matrix. -/
theorem selectedMatrixAction_selectedQuotientMorphism
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    {n : ℕ} (d : ℕ) (L : Matrix (Fin n) (Fin n) R) (hL : IsUnit L)
    (P : Module.Grassmannian A (Fin n → A) d) :
    selectedQuotientMorphism R P ≫ selectedMatrixAction R d L hL =
      selectedQuotientMorphism R
        (grassmannianTransport P
          ((L.map (algebraMap R A)).toLinearEquiv'
            (RingFlag.matrixBaseChange_isUnit L hL).invertible)) := by
  let p := selectedQuotientMorphism R P
  let M := (Scheme.Modules.pullback p).obj (selectedUniversalQuotientSheaf R n d)
  let q : coordinateFreeSheaf (Spec (CommRingCat.of A)) n ⟶ M :=
    (constantMatrixSheafIso R (p ≫ selectedChartSchemeToSpec R n d) L hL).inv ≫
      coordinatePullbackQuotient p (selectedUniversalQuotient R n d)
  let hfree := coordinateLocalFrames_pullback p (selectedUniversalQuotientSheaf R n d) d
    (selectedUniversalQuotient_over_frames R n d)
  let LA := L.map (algebraMap R A)
  let hLA : IsUnit LA := RingFlag.matrixBaseChange_isUnit L hL
  have hc : constantMatrixSheafIso R (p ≫ selectedChartSchemeToSpec R n d) L hL =
      constantMatrixSpecIso (CommRingCat.of A) LA hLA := by
    rw [show p ≫ selectedChartSchemeToSpec R n d =
        Spec.map (CommRingCat.ofHom (algebraMap R A)) from
      selectedQuotientMorphism_toSpec]
    apply Iso.ext
    exact constantMatrixSheafIso_specMap_hom R L hL A
  let e := selectedUniversalAffineQuotientIso R A P
  have hsource : q ≫ e.hom =
      (constantMatrixSpecIso (CommRingCat.of A) LA hLA).inv ≫
        coordinateQuotientSheafMap (CommRingCat.of A) P := by
    dsimp only [q, e]
    rw [Category.assoc]
    change (constantMatrixSheafIso R (p ≫ selectedChartSchemeToSpec R n d) L hL).inv ≫
      (selectedUniversalAffinePullbackQuotient R A P ≫
        (selectedUniversalAffineQuotientIso R A P).hom) = _
    rw [selectedUniversalAffineQuotientIso_source, hc]
  have hker : affineLocallyFreeGrassmannian (CommRingCat.of A) q d hfree =
      grassmannianTransport P (LA.toLinearEquiv' hLA.invertible) := by
    apply Module.Grassmannian.ext
    change LinearMap.ker (affineCoordinateQuotientMap (CommRingCat.of A) q) =
      Submodule.map (LA.toLinearEquiv' hLA.invertible).toLinearMap P.toSubmodule
    rw [← affineCoordinateQuotientMap_targetIso_ker (CommRingCat.of A) q e,
      hsource, affineCoordinateQuotientMap_constantMatrix_inv_ker,
      affineCoordinateQuotientMap_ker_of_coordinate]
  calc
    p ≫ selectedMatrixAction R d L hL =
        globalLocallyFreeQuotientMorphism R
          (p ≫ selectedChartSchemeToSpec R n d) q d hfree := by
      exact selectedMatrixAction_pullback R d L hL p
    _ = affineLocallyFreeQuotientMorphism R (CommRingCat.of A) q d hfree := by
      have hb : p ≫ selectedChartSchemeToSpec R n d =
          Spec.map (CommRingCat.ofHom (algebraMap R A)) :=
        selectedQuotientMorphism_toSpec
      exact (congrArg (fun b : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) =>
        globalLocallyFreeQuotientMorphism R b q d hfree) hb).trans
          (global_classifier_eq_affine R (CommRingCat.of A) q d hfree)
    _ = selectedQuotientMorphism R
          (grassmannianTransport P (LA.toLinearEquiv' hLA.invertible)) := by
      unfold affineLocallyFreeQuotientMorphism
      rw [hker]

/-- The same equality for an arbitrary original affine point over the base,
with its Grassmannian quotient recovered from that very morphism. -/
theorem selectedMatrixAction_affinePoint
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    {n : ℕ} (d : ℕ) (L : Matrix (Fin n) (Fin n) R) (hL : IsUnit L)
    (F : Spec (CommRingCat.of A) ⟶ selectedChartScheme R n d)
    (hF : F ≫ selectedChartSchemeToSpec R n d =
      Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    F ≫ selectedMatrixAction R d L hL =
      selectedQuotientMorphism R
        (grassmannianTransport (quotientOfSelectedMorphism F hF)
          ((L.map (algebraMap R A)).toLinearEquiv'
            (RingFlag.matrixBaseChange_isUnit L hL).invertible)) := by
  calc
    F ≫ selectedMatrixAction R d L hL =
        selectedQuotientMorphism R (quotientOfSelectedMorphism F hF) ≫
          selectedMatrixAction R d L hL := by
      exact congrArg (fun f => f ≫ selectedMatrixAction R d L hL)
        (selectedQuotientMorphism_quotientOfSelectedMorphism F hF).symm
    _ = _ := selectedMatrixAction_selectedQuotientMorphism R A d L hL _

/-- In quotient-rank `r` over a field, the scheme action is the
projective linear action on the original line, as an equality of morphisms. -/
theorem selectedMatrixAction_projectiveField
    (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    (r : ℕ) (L : Matrix (Fin (r+1)) (Fin (r+1)) R) (hL : IsUnit L)
    (p : Projectivization K (Fin (r+1) → K)) :
    (selectedProjectiveFieldEquiv R K r p).val ≫
        selectedMatrixAction R r L hL =
      (selectedProjectiveFieldEquiv R K r
        (Projectivization.map
          ((L.map (algebraMap R K)).toLinearEquiv'
            (RingFlag.matrixBaseChange_isUnit L hL).invertible).toLinearMap
          ((L.map (algebraMap R K)).toLinearEquiv'
            (RingFlag.matrixBaseChange_isUnit L hL).invertible).injective p)).val := by
  rw [selectedProjectiveFieldEquiv_val, selectedProjectiveFieldEquiv_val,
    selectedMatrixAction_selectedQuotientMorphism,
    projectiveGrassmannian_transport]

end FlagVarieties.Foundations.QuotientCharts
