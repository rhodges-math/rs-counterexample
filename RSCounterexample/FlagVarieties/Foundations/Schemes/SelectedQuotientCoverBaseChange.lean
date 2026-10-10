import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedQuotientMorphism

/-!
# Base change of the principal presentation cover

The principal elements and matrices extend along the given scalar tower.
The resulting cover presents the scalar-extended quotient, without
flatness. This is the cover used to compare the full scheme morphisms.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts.SelectedQuotientCover

open AlgebraicGeometry CategoryTheory

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {n d : ℕ} {P : Module.Grassmannian A (Fin n → A) d}
  (D : SelectedQuotientCover R A P)
  (B : Type u) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- The extension map on the coordinate ring of a principal open. -/
abbrev localBaseChange (i : D.index) :
    Localization.Away (D.element i) →ₐ[A]
      Localization.Away (algebraMap A B (D.element i)) :=
  Localization.awayMapₐ (IsScalarTower.toAlgHom A A B) (D.element i)

omit [Algebra R B] [IsScalarTower R A B] in
/-- Extended principal elements still generate the unit ideal. -/
theorem baseChange_span_top :
    Ideal.span (Set.range (fun i => algebraMap A B (D.element i))) = ⊤ := by
  have h := congrArg (Ideal.map (algebraMap A B)) D.span_top
  rw [Ideal.map_span, Ideal.map_top] at h
  simpa only [← Set.range_comp, Function.comp_def] using h

/-- Extension of a principal presentation cover is a cover of the extended quotient. -/
def baseChange : SelectedQuotientCover R B (coordinateGrassmannianBaseChange B P) where
  index := D.index
  element i := algebraMap A B (D.element i)
  selection := D.selection
  span_top := D.baseChange_span_top B
  evaluation i := ((D.localBaseChange B i).restrictScalars R).comp (D.evaluation i)
  represents i := by
    rw [D.represents_after_map i (D.localBaseChange B i),
      coordinateGrassmannianBaseChange_tower]

/-- The localized scalar map commutes with the two principal-open inclusions. -/
@[reassoc] theorem localBaseChange_square (i : D.index) :
    Spec.map (CommRingCat.ofHom (D.localBaseChange B i).toRingHom) ≫ D.schemeCover.f i =
      (D.baseChange B).schemeCover.f i ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) := by
  change Spec.map (CommRingCat.ofHom (D.localBaseChange B i).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (D.element i)))) =
    Spec.map (CommRingCat.ofHom
      (algebraMap B (Localization.Away (algebraMap A B (D.element i))))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A B))
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (D.localBaseChange B i).comp_algebraMap.trans (IsScalarTower.algebraMap_eq A B _)

/-- The extended local chart map is the composite of the original chart map with Spec. -/
theorem baseChange_chartMap (i : D.index) :
    (D.baseChange B).chartMap i =
      Spec.map (CommRingCat.ofHom (D.localBaseChange B i).toRingHom) ≫ D.chartMap i := by
  exact (selectedChartPointMap_comp R (D.selection i) (D.evaluation i)
    ((D.localBaseChange B i).restrictScalars R)).symm

end FlagVarieties.Foundations.QuotientCharts.SelectedQuotientCover
