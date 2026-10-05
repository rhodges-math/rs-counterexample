import Schubert.FlagVarieties.Foundations.Schemes.SelectedUniversalMorphismUniquenessAffine

/-!
# Uniqueness of arbitrary-scheme maps from the universal quotient

The source-preserving isomorphism is pulled to every affine open in
the canonical affine cover. Affine uniqueness there implies global equality.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory

universe u

/-- Pulling a target isomorphism back retains its equation on the original
labelled free source. -/
@[reassoc]
theorem coordinatePullbackQuotient_mapIso
    {X Y : Scheme.{u}} (j : X ⟶ Y) {M N : Y.Modules}
    {n : ℕ} (q : coordinateFreeSheaf Y n ⟶ M) (r : coordinateFreeSheaf Y n ⟶ N)
    (e : M ≅ N) (he : q ≫ e.hom = r) :
    coordinatePullbackQuotient j q ≫ (Scheme.Modules.pullback j).map e.hom =
      coordinatePullbackQuotient j r := by
  simp only [coordinatePullbackQuotient, Category.assoc, ← Functor.map_comp, he]

/-- A source-preserving comparison remains source-preserving after
restricting the two scheme morphisms along any further map. -/
def selectedUniversalMorphismComparisonRestrict
    (R : Type u) [CommRing R] {n d : ℕ} {X T : Scheme.{u}}
    (j : T ⟶ X) (F G : X ⟶ selectedChartScheme R n d)
    (e : (Scheme.Modules.pullback F).obj (selectedUniversalQuotientSheaf R n d) ≅
      (Scheme.Modules.pullback G).obj (selectedUniversalQuotientSheaf R n d)) :
    (Scheme.Modules.pullback (j ≫ F)).obj (selectedUniversalQuotientSheaf R n d) ≅
      (Scheme.Modules.pullback (j ≫ G)).obj (selectedUniversalQuotientSheaf R n d) :=
  ((Scheme.Modules.pullbackComp j F).app _).symm ≪≫
    (Scheme.Modules.pullback j).mapIso e ≪≫
    (Scheme.Modules.pullbackComp j G).app _

@[reassoc]
theorem selectedUniversalMorphismComparisonRestrict_source
    (R : Type u) [CommRing R] {n d : ℕ} {X T : Scheme.{u}}
    (j : T ⟶ X) (F G : X ⟶ selectedChartScheme R n d)
    (e : (Scheme.Modules.pullback F).obj (selectedUniversalQuotientSheaf R n d) ≅
      (Scheme.Modules.pullback G).obj (selectedUniversalQuotientSheaf R n d))
    (he : coordinatePullbackQuotient F (selectedUniversalQuotient R n d) ≫ e.hom =
      coordinatePullbackQuotient G (selectedUniversalQuotient R n d)) :
    coordinatePullbackQuotient (j ≫ F) (selectedUniversalQuotient R n d) ≫
      (selectedUniversalMorphismComparisonRestrict R j F G e).hom =
    coordinatePullbackQuotient (j ≫ G) (selectedUniversalQuotient R n d) := by
  simp only [selectedUniversalMorphismComparisonRestrict, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom]
  have hcompF := coordinatePullbackQuotient_comp j F (selectedUniversalQuotient R n d)
  have hcompG := coordinatePullbackQuotient_comp j G (selectedUniversalQuotient R n d)
  change (coordinatePullbackQuotient (j ≫ F) (selectedUniversalQuotient R n d) ≫
      (Scheme.Modules.pullbackComp j F).inv.app _) ≫
      (Scheme.Modules.pullback j).map e.hom ≫
      (Scheme.Modules.pullbackComp j G).hom.app _ = _
  rw [hcompF]
  rw [← Category.assoc]
  rw [coordinatePullbackQuotient_mapIso j _ _ e he]
  rw [← hcompG]
  simp

/-- The universal quotient with its original labelled source
determines any scheme morphism over the coefficient base. -/
theorem selectedUniversalMorphism_unique
    (R : Type u) [CommRing R] {n d : ℕ} {X : Scheme.{u}}
    (F G : X ⟶ selectedChartScheme R n d)
    (hbase : F ≫ selectedChartSchemeToSpec R n d =
      G ≫ selectedChartSchemeToSpec R n d)
    (e : (Scheme.Modules.pullback F).obj (selectedUniversalQuotientSheaf R n d) ≅
      (Scheme.Modules.pullback G).obj (selectedUniversalQuotientSheaf R n d))
    (he : coordinatePullbackQuotient F (selectedUniversalQuotient R n d) ≫ e.hom =
      coordinatePullbackQuotient G (selectedUniversalQuotient R n d)) : F = G := by
  let C := X.affineOpenCover
  apply C.openCover.hom_ext F G
  intro i
  let j := C.f i
  let A := C.X i
  let b : Spec A ⟶ Spec (CommRingCat.of R) :=
    (j ≫ F) ≫ selectedChartSchemeToSpec R n d
  letI : Algebra R A := (Spec.fullyFaithful.preimage b).unop.hom.toAlgebra
  have hb : Spec.map (CommRingCat.ofHom (algebraMap R A)) = b := by
    change Spec.map (Spec.fullyFaithful.preimage b).unop = b
    exact Spec.map_preimage_unop b
  have hF : (j ≫ F) ≫ selectedChartSchemeToSpec R n d =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := hb.symm
  have hG : (j ≫ G) ≫ selectedChartSchemeToSpec R n d =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    calc
      (j ≫ G) ≫ selectedChartSchemeToSpec R n d =
          j ≫ (G ≫ selectedChartSchemeToSpec R n d) := Category.assoc _ _ _
      _ = j ≫ (F ≫ selectedChartSchemeToSpec R n d) := by rw [hbase]
      _ = Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
        rw [← Category.assoc]
        exact hF
  exact selectedUniversalMorphism_unique_affine R A (j ≫ F) (j ≫ G) hF hG
    (selectedUniversalMorphismComparisonRestrict R j F G e)
    (selectedUniversalMorphismComparisonRestrict_source R j F G e he)

end FlagVarieties.Foundations.QuotientCharts
