import RSCounterexample.FlagVarieties.Foundations.Schemes.GeneralLinearGrassmannianAffine

/-! Evaluation of the varying general-linear morphism on every
affine point of the relative product. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory ModuleSheafGluing
universe u

private theorem affineClassifier_eq_global (R B : Type u)
    [CommRing R] [CommRing B] [Algebra R B] {n : ℕ}
    {M : (Spec (CommRingCat.of B)).Modules}
    (q : coordinateFreeSheaf (Spec (CommRingCat.of B)) n ⟶ M) [Epi q] (d : ℕ)
    (hf : ∀ p : Spec (CommRingCat.of B), ∃ U : (Spec (CommRingCat.of B)).Opens,
      p ∈ U ∧ Nonempty (M.over U ≅
        SheafOfModules.free (R := (Spec (CommRingCat.of B)).ringCatSheaf.over U)
          (CoordinateIndex.{u} d))) :
    globalLocallyFreeQuotientMorphism R
      (Spec.map (CommRingCat.ofHom (algebraMap R B))) q d hf =
    affineLocallyFreeQuotientMorphism R (CommRingCat.of B) q d hf := by
  exact affineLocallyFreeQuotientMorphism_unique R (CommRingCat.of B) q d hf _
    (globalLocallyFreeQuotientMorphism_toSpec R _ q d hf)
    (globalLocallyFreeUniversalIso R _ q d hf)
    (globalLocallyFreeUniversalIso_source R _ q d hf)

private theorem affineKernel_targetIso
    (B : CommRingCat.{u}) {n : ℕ} {M N : (Spec B).Modules}
    (q : coordinateFreeSheaf (Spec B) n ⟶ M) (e : M ≅ N) :
    LinearMap.ker (affineCoordinateQuotientMap B (q ≫ e.hom)) =
      LinearMap.ker (affineCoordinateQuotientMap B q) := by
  have hm : affineCoordinateQuotientMap B (q ≫ e.hom) =
      (moduleSpecΓFunctor.map e.hom).hom.comp (affineCoordinateQuotientMap B q) := by
    apply LinearMap.ext
    intro x
    change (moduleSpecΓFunctor.map (q ≫ e.hom)).hom
      ((coordinateFreeGlobalIso B n).hom.hom x) = _
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

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
  (n d : ℕ)
  (k : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] B)
  (P : Module.Grassmannian B (Fin n → B) d)

/-- The universal matrix is evaluated entrywise at `k`, and its forward
linear action transports the original ambient kernel. This is equality of
`Spec B → Grass_R` morphisms, not just equality on underlying points. -/
theorem generalLinearGrassmannianAction_evaluate :
    generalLinearGrassmannianOfAffine R B n d k P ≫
        generalLinearGrassmannianAction R n d =
      selectedQuotientMorphism R
        (grassmannianTransport P
          ((generalLinearMatrixAt R B n k).toLinearEquiv'
            (generalLinearMatrixAt_isUnit R B n k).invertible)) := by
  let f := generalLinearGrassmannianOfAffine R B n d k P
  let T := (Scheme.Modules.pullback (generalLinearGrassmannianPoint R n d)).obj
    (selectedUniversalQuotientSheaf R n d)
  let q := coordinatePullbackQuotient f (generalLinearGrassmannianQuotient R n d)
  let hf := coordinateLocalFrames_pullback f T d
    (coordinateLocalFrames_pullback (generalLinearGrassmannianPoint R n d)
      (selectedUniversalQuotientSheaf R n d) d
      (selectedUniversalQuotient_over_frames R n d))
  let e := generalLinearGrassmannianAffineTargetIso R B n d k P
  let Lk := generalLinearMatrixAt R B n k
  let hLk := generalLinearMatrixAt_isUnit R B n k
  have hsource : q ≫ e.hom =
      (constantMatrixSpecIso (CommRingCat.of B) Lk hLk).inv ≫
        coordinateQuotientSheafMap (CommRingCat.of B) P :=
    generalLinearGrassmannianAffineQuotient_source R B n d k P
  have hker : affineLocallyFreeGrassmannian (CommRingCat.of B) q d hf =
      grassmannianTransport P (Lk.toLinearEquiv' hLk.invertible) := by
    apply Module.Grassmannian.ext
    change LinearMap.ker (affineCoordinateQuotientMap (CommRingCat.of B) q) =
      Submodule.map (Lk.toLinearEquiv' hLk.invertible).toLinearMap P.toSubmodule
    rw [← affineKernel_targetIso (CommRingCat.of B) q e, hsource,
      affineCoordinateQuotientMap_constantMatrix_inv_ker,
      affineCoordinateQuotientMap_ker_of_coordinate]
  have hb : f ≫ generalLinearGrassmannianToSpec R n d =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
    change (f ≫ generalLinearGrassmannianPoint R n d) ≫
      selectedChartSchemeToSpec R n d = _
    rw [generalLinearGrassmannianOfAffine_point]
    exact selectedQuotientMorphism_toSpec
  calc
    f ≫ generalLinearGrassmannianAction R n d =
        globalLocallyFreeQuotientMorphism R
          (f ≫ generalLinearGrassmannianToSpec R n d) q d hf := by
      exact generalLinearGrassmannianAction_pullback R n d f
    _ = globalLocallyFreeQuotientMorphism R
          (Spec.map (CommRingCat.ofHom (algebraMap R B))) q d hf := by
      exact congrArg (fun b : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R) =>
        globalLocallyFreeQuotientMorphism R b q d hf) hb
    _ = affineLocallyFreeQuotientMorphism R (CommRingCat.of B) q d hf :=
      affineClassifier_eq_global R B q d hf
    _ = selectedQuotientMorphism R
          (grassmannianTransport P (Lk.toLinearEquiv' hLk.invertible)) := by
      unfold affineLocallyFreeQuotientMorphism
      rw [hker]

end FlagVarieties.Foundations.QuotientCharts
