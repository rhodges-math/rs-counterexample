import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedSheafBaseChange

/-!
# Open restriction of selected quotient sheaves

Restriction is compared with pullback by Mathlib's canonical natural
isomorphism. Both the quotient maps and the target transition isomorphisms
therefore retain their original coordinates under affine open restriction.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- Canonical unit-sheaf comparison for open restriction, through the
canonical restriction/pullback identification. -/
def coordinateRestrictionUnitIso {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] :
    (QuotientPair.unitSheaf X).restrict f ≅ QuotientPair.unitSheaf Y :=
  (Scheme.Modules.restrictFunctorIsoPullback f).app (QuotientPair.unitSheaf X) ≪≫
    QuotientPair.quotientPullbackUnitIso f

/-- The original labelled free sheaf under open restriction. -/
def coordinateRestrictionIso {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] (n : ℕ) :
    (coordinateFreeSheaf X n).restrict f ≅ coordinateFreeSheaf Y n :=
  (Scheme.Modules.restrictFunctorIsoPullback f).app (coordinateFreeSheaf X n) ≪≫
    coordinatePullbackIso f n

/-- Every original summand is retained by the canonical open-restriction comparison. -/
@[reassoc]
theorem coordinateRestrictionIso_generator {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] {n : ℕ} (i : CoordinateIndex.{u} n) :
    (Scheme.Modules.restrictFunctor f).map (SheafOfModules.ιFree i) ≫
      (coordinateRestrictionIso f n).hom =
    (coordinateRestrictionUnitIso f).hom ≫ SheafOfModules.ιFree i := by
  change (Scheme.Modules.restrictFunctor f).map (SheafOfModules.ιFree i) ≫
      (Scheme.Modules.restrictFunctorIsoPullback f).hom.app (coordinateFreeSheaf X n) ≫
        (coordinatePullbackIso f n).hom = _
  rw [← Category.assoc, (Scheme.Modules.restrictFunctorIsoPullback f).hom.naturality,
    Category.assoc, coordinatePullbackIso_generator]
  rfl

variable (R : Type u) [CommRing R] (A B : CommRingCat.{u}) [Algebra R A] [Algebra R B]
  {n d : ℕ} (a b : Fin d ↪ Fin n)
  (f g : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A) (k : A →ₐ[R] B)
  [IsOpenImmersion (Spec.map (CommRingCat.ofHom k.toRingHom))]

/-- The restriction of a selected presentation, under the canonical
free-source and free-target comparisons. -/
@[reassoc]
theorem selectedPresentationSheafMap_restrict :
    (Scheme.Modules.restrictFunctor (Spec.map (CommRingCat.ofHom k.toRingHom))).map
        (selectedPresentationSheafMap R A a f) ≫
      (coordinateRestrictionIso (Spec.map (CommRingCat.ofHom k.toRingHom)) d).hom =
    (coordinateRestrictionIso (Spec.map (CommRingCat.ofHom k.toRingHom)) n).hom ≫
      selectedPresentationSheafMap R B a (k.comp f) := by
  change (Scheme.Modules.restrictFunctor _).map (selectedPresentationSheafMap R A a f) ≫
      (Scheme.Modules.restrictFunctorIsoPullback _).hom.app (coordinateFreeSheaf (Spec A) d) ≫
        (coordinatePullbackIso _ d).hom = _
  rw [← Category.assoc, (Scheme.Modules.restrictFunctorIsoPullback _).hom.naturality,
    Category.assoc, selectedPresentationSheafMap_pullback]
  rfl

/-- The original target transition under open restriction. -/
@[reassoc]
theorem selectedPresentationSheafTransition_restrict
    (he : selectedChartPoint R a f = selectedChartPoint R b g) :
    (Scheme.Modules.restrictFunctor (Spec.map (CommRingCat.ofHom k.toRingHom))).map
        (selectedPresentationSheafTransition R A a b f g he).hom ≫
      (coordinateRestrictionIso (Spec.map (CommRingCat.ofHom k.toRingHom)) d).hom =
    (coordinateRestrictionIso (Spec.map (CommRingCat.ofHom k.toRingHom)) d).hom ≫
      (selectedPresentationSheafTransition R B a b (k.comp f) (k.comp g)
        (selectedPresentation_point_map R a b f g k he)).hom := by
  change (Scheme.Modules.restrictFunctor _).map
      (selectedPresentationSheafTransition R A a b f g he).hom ≫
      (Scheme.Modules.restrictFunctorIsoPullback _).hom.app (coordinateFreeSheaf (Spec A) d) ≫
        (coordinatePullbackIso _ d).hom = _
  rw [← Category.assoc, (Scheme.Modules.restrictFunctorIsoPullback _).hom.naturality,
    Category.assoc, selectedPresentationSheafTransition_pullback]
  rfl

end FlagVarieties.Foundations.QuotientCharts
