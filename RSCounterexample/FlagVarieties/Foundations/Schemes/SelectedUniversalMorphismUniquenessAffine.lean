import RSCounterexample.FlagVarieties.Foundations.Schemes.AffineLocallyFreeUniversalClassification
import RSCounterexample.FlagVarieties.Foundations.Schemes.CoordinateLocalFramesPullback

/-!
# Uniqueness of affine maps from their universal quotient

Two affine maps over the coefficient base agree when their universal
quotient pullbacks are isomorphic over the original labelled free source.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory

universe u

/-- The universal quotient has rank-d frames on an open around every point. -/
theorem selectedUniversalQuotient_over_frames (R : Type u) [CommRing R] (n d : ℕ)
    (y : selectedChartScheme R n d) :
    ∃ U : (selectedChartScheme R n d).Opens, y ∈ U ∧
      Nonempty ((selectedUniversalQuotientSheaf R n d).over U ≅
        SheafOfModules.free
          (R := (selectedChartScheme R n d).ringCatSheaf.over U)
          (CoordinateIndex.{u} d)) := by
  obtain ⟨U, hy, ⟨e⟩⟩ := selectedUniversalQuotient_local_frames R n d y
  exact ⟨U, hy, ⟨ModuleSheafGluing.coordinateOverFrame _ U d e⟩⟩

/-- The universal quotient stays rank-d locally free after any scheme pullback. -/
theorem selectedUniversalQuotient_pullback_over_frames
    (R : Type u) [CommRing R] (n d : ℕ) {X : Scheme.{u}}
    (F : X ⟶ selectedChartScheme R n d) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      Nonempty (((Scheme.Modules.pullback F).obj
        (selectedUniversalQuotientSheaf R n d)).over U ≅
        SheafOfModules.free (R := X.ringCatSheaf.over U) (CoordinateIndex.{u} d)) :=
  ModuleSheafGluing.coordinateLocalFrames_pullback F
    (selectedUniversalQuotientSheaf R n d) d
    (selectedUniversalQuotient_over_frames R n d) x

/-- The source-preserving quotient determines an incoming affine map. -/
theorem selectedUniversalMorphism_unique_affine
    (R : Type u) [CommRing R] (A : CommRingCat.{u}) [Algebra R A]
    {n d : ℕ}
    (F G : Spec A ⟶ selectedChartScheme R n d)
    (hF : F ≫ selectedChartSchemeToSpec R n d =
      Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (hG : G ≫ selectedChartSchemeToSpec R n d =
      Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (e : (Scheme.Modules.pullback F).obj (selectedUniversalQuotientSheaf R n d) ≅
      (Scheme.Modules.pullback G).obj (selectedUniversalQuotientSheaf R n d))
    (he : coordinatePullbackQuotient F (selectedUniversalQuotient R n d) ≫ e.hom =
      coordinatePullbackQuotient G (selectedUniversalQuotient R n d)) : F = G := by
  let q := coordinatePullbackQuotient G (selectedUniversalQuotient R n d)
  haveI : Epi q := inferInstance
  let hfree := selectedUniversalQuotient_pullback_over_frames R n d G
  have h₁ : F = affineLocallyFreeQuotientMorphism R A q d hfree :=
    affineLocallyFreeQuotientMorphism_unique R A q d hfree F hF e he
  have h₂ : G = affineLocallyFreeQuotientMorphism R A q d hfree :=
    affineLocallyFreeQuotientMorphism_unique R A q d hfree G hG (Iso.refl _) (by simp [q])
  exact h₁.trans h₂.symm

end FlagVarieties.Foundations.QuotientCharts
