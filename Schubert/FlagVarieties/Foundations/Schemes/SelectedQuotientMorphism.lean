import Schubert.FlagVarieties.Foundations.Schemes.SelectedQuotientCoverOverlap

/-!
# A scheme morphism from every finite-projective coordinate quotient

Principal presentations exist for the quotient and their overlap maps
agree. Gluing therefore yields a morphism to the selected-chart scheme.
The result is independent of the chosen cover and normalized presentations.
The converse classification of scheme morphisms by quotients is
`Schemes/SelectedAffineClassification.lean` (affine sources) and
`Schemes/GlobalLocallyFreeQuotient.lean` (arbitrary schemes).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {n d : ℕ} {P : Module.Grassmannian A (Fin n → A) d}

namespace SelectedQuotientCover

variable (D E : SelectedQuotientCover R A P)

/-- The global scheme map obtained from a quotient's local presentations. -/
def toScheme : Spec (CommRingCat.of A) ⟶ selectedChartScheme R n d :=
  D.schemeCover.glueMorphisms D.chartMap (D.overlap D)

/-- Its restriction is the original normalized quotient presentation. -/
@[reassoc (attr := simp)] theorem ι_toScheme (i : D.index) :
    D.schemeCover.f i ≫ D.toScheme = D.chartMap i :=
  D.schemeCover.ι_glueMorphisms D.chartMap (D.overlap D) i

/-- Two independently chosen covers and presentations give the same full scheme map. -/
theorem toScheme_independent : D.toScheme = E.toScheme := by
  apply D.schemeCover.hom_ext
  intro i
  rw [D.ι_toScheme]
  apply Scheme.Cover.hom_ext (E.schemeCover.pullback₁ (D.schemeCover.f i))
  intro j
  change pullback.fst (D.schemeCover.f i) (E.schemeCover.f j) ≫ D.chartMap i =
    pullback.fst (D.schemeCover.f i) (E.schemeCover.f j) ≫ D.schemeCover.f i ≫ E.toScheme
  rw [pullback.condition_assoc, E.ι_toScheme]
  exact D.overlap E i j

/-- The global map respects the original coefficient ring. -/
@[reassoc] theorem toScheme_toSpec :
    D.toScheme ≫ selectedChartSchemeToSpec R n d =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  apply D.schemeCover.hom_ext
  intro i
  rw [← Category.assoc, D.ι_toScheme, chartMap, selectedChartPointMap_toSpec]
  exact (spec_map_algHom_toSpec R
    (IsScalarTower.toAlgHom R A (Localization.Away (D.element i)))).symm

end SelectedQuotientCover

/-- Every finite-projective quotient determines a map to the glued chart scheme. -/
def selectedQuotientMorphism (R : Type u) [CommRing R] {A : Type u}
    [CommRing A] [Algebra R A] {n d : ℕ}
    (P : Module.Grassmannian A (Fin n → A) d) :
    Spec (CommRingCat.of A) ⟶ selectedChartScheme R n d :=
  (selectedQuotientCover R A P).toScheme

/-- Any valid local presentation cover computes the unconditional quotient morphism. -/
theorem SelectedQuotientCover.toScheme_eq (D : SelectedQuotientCover R A P) :
    D.toScheme = selectedQuotientMorphism R P :=
  D.toScheme_independent (selectedQuotientCover R A P)

/-- Local presentations compute the unconditional map without a chosen global basis. -/
@[reassoc] theorem SelectedQuotientCover.ι_selectedQuotientMorphism
    (D : SelectedQuotientCover R A P) (i : D.index) :
    D.schemeCover.f i ≫ selectedQuotientMorphism R P = D.chartMap i := by
  rw [← D.toScheme_eq, D.ι_toScheme]

/-- The unconditional quotient map is a morphism over the coefficient base. -/
@[reassoc] theorem selectedQuotientMorphism_toSpec :
    selectedQuotientMorphism R P ≫ selectedChartSchemeToSpec R n d =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) :=
  (selectedQuotientCover R A P).toScheme_toSpec

end FlagVarieties.Foundations.QuotientCharts
