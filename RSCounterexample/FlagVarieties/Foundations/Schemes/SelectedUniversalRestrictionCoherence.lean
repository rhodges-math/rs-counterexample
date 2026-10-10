import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedSheafRestrictionComparison
import RSCounterexample.FlagVarieties.Foundations.Schemes.ModuleSheafGluingRestriction

/-!
# Canonical free-sheaf restriction coherence

The unit comparison respects composition of open immersions, by the
structure sheaf's `appIso` composition formula. Preserved coproduct generators
then give the same coherence for every original finite coordinate free sheaf.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [IsOpenImmersion f] [IsOpenImmersion g]

/-- Unit-sheaf restriction respects composition. -/
@[reassoc]
theorem coordinateRestrictUnit_comp :
    (Scheme.Modules.restrictFunctorComp f g).hom.app (QuotientPair.unitSheaf Z) ≫
      (Scheme.Modules.restrictFunctor f).map (Scheme.Modules.restrictUnitIso g).hom ≫
        (Scheme.Modules.restrictUnitIso f).hom =
    (Scheme.Modules.restrictUnitIso (f ≫ g)).hom := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change (f.appIso U).hom ((g.appIso (f ''ᵁ U)).hom
    (Z.presheaf.map (eqToHom (by simp)).op x)) = ((f ≫ g).appIso U).hom x
  rw [Scheme.Hom.comp_appIso]
  rfl

/-- The standard free-sheaf restriction comparison preserves each original generator. -/
@[reassoc]
theorem coordinateRestrictFreeIso_generator (n : ℕ) (i : CoordinateIndex.{u} n) :
    (Scheme.Modules.restrictFunctor f).map (SheafOfModules.ιFree i) ≫
      (coordinateRestrictFreeIso f n).hom =
    (Scheme.Modules.restrictUnitIso f).hom ≫ SheafOfModules.ιFree i := by
  rw [← coordinateRestrictionIso_eq, ← coordinateRestrictionUnitIso_eq]
  exact coordinateRestrictionIso_generator f i

/-- The labelled free-sheaf comparison respects composition of open immersions. -/
@[reassoc]
theorem coordinateRestrictFreeIso_comp (n : ℕ) :
    (Scheme.Modules.restrictFunctorComp f g).hom.app (coordinateFreeSheaf Z n) ≫
      (Scheme.Modules.restrictFunctor f).map (coordinateRestrictFreeIso g n).hom ≫
        (coordinateRestrictFreeIso f n).hom =
    (coordinateRestrictFreeIso (f ≫ g) n).hom := by
  apply Cofan.IsColimit.hom_ext
    (isColimitCofanMkObjOfIsColimit (Scheme.Modules.restrictFunctor (f ≫ g)) _ _
      (SheafOfModules.isColimitFreeCofan (R := Z.ringCatSheaf) (CoordinateIndex.{u} n)))
  intro i
  change (Scheme.Modules.restrictFunctor (f ≫ g)).map (SheafOfModules.ιFree i) ≫
      (Scheme.Modules.restrictFunctorComp f g).hom.app (coordinateFreeSheaf Z n) ≫
      (Scheme.Modules.restrictFunctor f).map (coordinateRestrictFreeIso g n).hom ≫
      (coordinateRestrictFreeIso f n).hom =
    (Scheme.Modules.restrictFunctor (f ≫ g)).map (SheafOfModules.ιFree i) ≫
      (coordinateRestrictFreeIso (f ≫ g) n).hom
  rw [← Category.assoc _ ((Scheme.Modules.restrictFunctorComp f g).hom.app _),
    (Scheme.Modules.restrictFunctorComp f g).hom.naturality]
  simp only [Functor.comp_map, Category.assoc]
  rw [← Functor.map_comp_assoc, coordinateRestrictFreeIso_generator,
    Functor.map_comp, Category.assoc, coordinateRestrictFreeIso_generator,
    coordinateRestrictFreeIso_generator]
  simpa only [Category.assoc] using congrArg
    (fun t => t ≫ SheafOfModules.ιFree i) (coordinateRestrictUnit_comp f g)

/-- The standard unit comparison at the identity is the canonical restriction identity. -/
theorem coordinateRestrictUnit_id :
    (Scheme.Modules.restrictUnitIso (𝟙 X)).hom =
      (Scheme.Modules.restrictFunctorId.app (QuotientPair.unitSheaf X)).hom := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change ((𝟙 X : X ⟶ X).appIso U).hom x =
    X.presheaf.map (eqToHom (show U = 𝟙 X ''ᵁ U by simp)).op x
  rw [Scheme.Hom.id_appIso]
  rfl

/-- The standard labelled free comparison at the identity is canonical. -/
theorem coordinateRestrictFreeIso_id (n : ℕ) :
    coordinateRestrictFreeIso (𝟙 X) n =
      Scheme.Modules.restrictFunctorId.app (coordinateFreeSheaf X n) := by
  apply Iso.ext
  apply Cofan.IsColimit.hom_ext
    (isColimitCofanMkObjOfIsColimit (Scheme.Modules.restrictFunctor (𝟙 X)) _ _
      (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) (CoordinateIndex.{u} n)))
  intro i
  change (Scheme.Modules.restrictFunctor (𝟙 X)).map (SheafOfModules.ιFree i) ≫
      (coordinateRestrictFreeIso (𝟙 X) n).hom =
    (Scheme.Modules.restrictFunctor (𝟙 X)).map (SheafOfModules.ιFree i) ≫
      (Scheme.Modules.restrictFunctorId.app (coordinateFreeSheaf X n)).hom
  rw [coordinateRestrictFreeIso_generator, coordinateRestrictUnit_id]
  exact (Scheme.Modules.restrictFunctorId.hom.naturality (SheafOfModules.ιFree i)).symm

/-- Equal open-immersion morphisms give the same canonical free comparison. -/
theorem coordinateRestrictFreeIso_congr {f' : X ⟶ Y} [IsOpenImmersion f'] (h : f = f')
    (n : ℕ) :
    (Scheme.Modules.restrictFunctorCongr h).hom.app (coordinateFreeSheaf Y n) ≫
      (coordinateRestrictFreeIso f' n).hom = (coordinateRestrictFreeIso f n).hom := by
  subst f'
  have he : (Scheme.Modules.restrictFunctorCongr (rfl : f = f)).hom.app
      (coordinateFreeSheaf Y n) = 𝟙 _ := by
    apply Scheme.Modules.hom_ext
    intro U
    simp
    rfl
  rw [he, Category.id_comp]

/-- The common-source identification used by gluing retains the original free
coordinates after passing through a containing chart. -/
@[reassoc]
theorem coordinateRestrictFreeIso_through {V W : X.Opens} (h : W ≤ V) (n : ℕ) :
    (ModuleSheafGluing.restrictionThroughChart h).hom.app (coordinateFreeSheaf X n) ≫
      (Scheme.Modules.restrictFunctor (X.homOfLE h)).map (coordinateRestrictFreeIso V.ι n).hom ≫
        (coordinateRestrictFreeIso (X.homOfLE h) n).hom =
    (coordinateRestrictFreeIso W.ι n).hom := by
  simp only [ModuleSheafGluing.restrictionThroughChart, Iso.trans_hom,
    NatTrans.comp_app, Category.assoc]
  rw [coordinateRestrictFreeIso_comp, coordinateRestrictFreeIso_congr]

end FlagVarieties.Foundations.QuotientCharts
