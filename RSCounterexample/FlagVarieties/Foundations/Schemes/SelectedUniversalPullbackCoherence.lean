import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedUniversalQuotient

/-!
# Canonical free-sheaf coherence for arbitrary geometric pullback

The composition comparison is related to the pushforward comparison
by adjunction. This identifies the canonical unit map, hence every original
free-sheaf generator, under arbitrary composition of scheme morphisms.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Adjunction identifies the canonical composition comparison with the
composition of pushforward functors. -/
theorem coordinatePullbackComp_adjoint (M : Z.Modules) (N : X.Modules)
    (q : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) ⟶ N) :
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv M N
      ((Scheme.Modules.pullbackComp f g).inv.app M ≫ q) =
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f)).homEquiv M N q ≫
        (Scheme.Modules.pushforwardComp f g).hom.app N := by
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  simp only [Adjunction.homEquiv_apply, Functor.map_comp, ← Category.assoc]
  rw [← h, Category.assoc, ← (Scheme.Modules.pushforwardComp f g).hom.naturality]
  simp only [Category.assoc]

/-- The canonical unit map for a composite is exactly the composite of the
canonical pullback unit maps. -/
@[reassoc]
theorem coordinatePullbackUnit_comp :
    (Scheme.Modules.pullbackComp f g).inv.app (QuotientPair.unitSheaf Z) ≫
      (Scheme.Modules.pullback f).map (QuotientPair.quotientPullbackUnitIso g).hom ≫
        (QuotientPair.quotientPullbackUnitIso f).hom =
      (QuotientPair.quotientPullbackUnitIso (f ≫ g)).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _).injective
  rw [coordinatePullbackComp_adjoint]
  rw [Adjunction.comp_homEquiv]
  change (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        ((Scheme.Modules.pullback f).map (QuotientPair.quotientPullbackUnitIso g).hom ≫
          (QuotientPair.quotientPullbackUnitIso f).hom)) ≫
      (Scheme.Modules.pushforwardComp f g).hom.app _ = _
  rw [Adjunction.homEquiv_naturality_left]
  have hf : (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      (QuotientPair.quotientPullbackUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have hg : (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
      (QuotientPair.quotientPullbackUnitIso g).hom =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have hfg : (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _
      (QuotientPair.quotientPullbackUnitIso (f ≫ g)).hom =
      SheafOfModules.unitToPushforwardObjUnit (f ≫ g).toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  rw [hf, Adjunction.homEquiv_naturality_right, hg, hfg]
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  rfl

/-- Arbitrary pullback composition retains the canonical labelled free-sheaf comparison. -/
@[reassoc]
theorem coordinatePullbackFreeIso_comp (n : ℕ) :
    (Scheme.Modules.pullbackComp f g).inv.app (coordinateFreeSheaf Z n) ≫
      (Scheme.Modules.pullback f).map (coordinatePullbackFreeIso g n).hom ≫
        (coordinatePullbackFreeIso f n).hom =
      (coordinatePullbackFreeIso (f ≫ g) n).hom := by
  apply Cofan.IsColimit.hom_ext
    (isColimitCofanMkObjOfIsColimit (Scheme.Modules.pullback (f ≫ g)) _ _
      (SheafOfModules.isColimitFreeCofan (R := Z.ringCatSheaf) (CoordinateIndex.{u} n)))
  intro i
  change (Scheme.Modules.pullback (f ≫ g)).map (SheafOfModules.ιFree i) ≫
      (Scheme.Modules.pullbackComp f g).inv.app (coordinateFreeSheaf Z n) ≫
      (Scheme.Modules.pullback f).map (coordinatePullbackFreeIso g n).hom ≫
      (coordinatePullbackFreeIso f n).hom =
    (Scheme.Modules.pullback (f ≫ g)).map (SheafOfModules.ιFree i) ≫
      (coordinatePullbackFreeIso (f ≫ g) n).hom
  rw [← Category.assoc _ ((Scheme.Modules.pullbackComp f g).inv.app _),
    (Scheme.Modules.pullbackComp f g).inv.naturality]
  simp only [Functor.comp_map, Category.assoc]
  rw [← Functor.map_comp_assoc]
  simp only [← coordinatePullbackIso_eq, coordinatePullbackIso_generator,
    Functor.map_comp, Category.assoc]
  simpa only [Category.assoc] using congrArg
    (fun t => t ≫ SheafOfModules.ιFree i) (coordinatePullbackUnit_comp f g)

end FlagVarieties.Foundations.QuotientCharts
