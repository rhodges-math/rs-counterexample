import Schubert.FlagVarieties.Foundations.Schemes.AffineLocallyFreeUniversalQuotient
import Schubert.FlagVarieties.Foundations.Schemes.SelectedUniversalAffineMorphism

/-!
# The affine universal property for locally free quotient sheaves

Every affine rank-d locally free quotient of the labelled free
sheaf is the pullback of the universal quotient along exactly one
morphism over the coefficient base. The source map is part of the
comparison, so target isomorphism alone is never substituted for a
quotient-family isomorphism.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] (A : CommRingCat.{u}) [Algebra R A]
  {n : ℕ} {M : (Spec A).Modules}
  (q : coordinateFreeSheaf (Spec A) n ⟶ M) [Epi q] (d : ℕ)
  (hfree : ∀ p : Spec A, ∃ U : (Spec A).Opens, p ∈ U ∧
    Nonempty (M.over U ≅
      SheafOfModules.free (R := (Spec A).ringCatSheaf.over U) (CoordinateIndex.{u} d)))

theorem affineLocallyFreeQuotientMorphism_unique
    (F : Spec A ⟶ selectedChartScheme R n d)
    (hF : F ≫ selectedChartSchemeToSpec R n d =
      Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (e : (Scheme.Modules.pullback F).obj (selectedUniversalQuotientSheaf R n d) ≅ M)
    (he : coordinatePullbackQuotient F (selectedUniversalQuotient R n d) ≫ e.hom = q) :
    F = affineLocallyFreeQuotientMorphism R A q d hfree := by
  let P := quotientOfSelectedMorphism F hF
  let c := selectedUniversalAffineMorphismIso F hF
  have hc : coordinatePullbackQuotient F (selectedUniversalQuotient R n d) ≫ c.hom =
      coordinateQuotientSheafMap A P := selectedUniversalAffineMorphismIso_source F hF
  have hs : coordinateQuotientSheafMap A P ≫ (c.symm ≪≫ e).hom = q := by
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [← hc]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using he
  have hP : P = affineLocallyFreeGrassmannian A q d hfree :=
    affineLocallyFreeGrassmannian_unique A q d hfree P (c.symm ≪≫ e) hs
  calc
    F = selectedQuotientMorphism R P :=
      (selectedQuotientMorphism_quotientOfSelectedMorphism F hF).symm
    _ = affineLocallyFreeQuotientMorphism R A q d hfree := by
      rw [hP]
      rfl

include hfree

/-- The full affine universal property, expressed with quotient sheaves. -/
theorem affineLocallyFreeUniversal_existsUnique :
    ∃! F : {F : Spec A ⟶ selectedChartScheme R n d //
      F ≫ selectedChartSchemeToSpec R n d =
        Spec.map (CommRingCat.ofHom (algebraMap R A))},
      ∃ e : (Scheme.Modules.pullback F.val).obj (selectedUniversalQuotientSheaf R n d) ≅ M,
        coordinatePullbackQuotient F.val (selectedUniversalQuotient R n d) ≫ e.hom = q := by
  refine ⟨⟨affineLocallyFreeQuotientMorphism R A q d hfree,
    affineLocallyFreeQuotientMorphism_toSpec R A q d hfree⟩,
    ⟨affineLocallyFreeUniversalQuotientIso R A q d hfree,
      affineLocallyFreeUniversalQuotientIso_source R A q d hfree⟩, ?_⟩
  rintro F ⟨e, he⟩
  exact Subtype.ext (affineLocallyFreeQuotientMorphism_unique R A q d hfree F.val F.property e he)

end FlagVarieties.Foundations.QuotientCharts
