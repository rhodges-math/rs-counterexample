import RSCounterexample.FlagVarieties.Foundations.Schemes.CoordinateSheafGenerators
import RSCounterexample.FlagVarieties.Foundations.Schemes.QuotientLineSheafPullback

/-!
# Pullback of scalar maps and labelled free sheaves

Scalar multiplication on the unit sheaf is obtained from the associated
sheaf functor. Its pullback compatibility uses the structure-sheaf map
of `Spec.map` and the sheaf pullback adjunction.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- Multiplication on the original scalar module. -/
def scalarLinear (A : CommRingCat.{u}) (r : A) : A →ₗ[A] A :=
  (LinearMap.id : A →ₗ[A] A).smulRight r

/-- The associated scalar endomorphism of the unit sheaf. -/
def affineScalarSheafMap (A : CommRingCat.{u}) (r : A) :
    QuotientPair.unitSheaf (Spec A) ⟶ QuotientPair.unitSheaf (Spec A) :=
  tilde.map (ModuleCat.ofHom (scalarLinear A r))

/-- The scalar associated-sheaf map acts by multiplication by the
structure-sheaf section, on every open. -/
theorem affineScalarSheafMap_app (A : CommRingCat.{u}) (r : A)
    (U : (Spec A).Opens) (x : Γ(Spec A, U)) :
    (affineScalarSheafMap A r).app U x = x * algebraMap A Γ(Spec A, U) r := by
  have h := ConcreteCategory.congr_hom
    (tilde.toOpen_map_app (ModuleCat.ofHom (scalarLinear A r)) U) (1 : A)
  have h1 : (tilde.toOpen (ModuleCat.of A A) U) (1 : A) = (1 : Γ(Spec A, U)) := by
    change (algebraMap A Γ(Spec A, U)) 1 = 1
    exact map_one _
  change (affineScalarSheafMap A r).app U
      ((tilde.toOpen (ModuleCat.of A A) U) 1) =
    (tilde.toOpen (ModuleCat.of A A) U) (scalarLinear A r 1) at h
  rw [h1] at h
  have hr' : (tilde.toOpen (ModuleCat.of A A) U) r = algebraMap A Γ(Spec A, U) r := by
    calc
      (tilde.toOpen (ModuleCat.of A A) U) r =
          (tilde.toOpen (ModuleCat.of A A) U) (r • (1 : A)) := by simp
      _ = r • (tilde.toOpen (ModuleCat.of A A) U) (1 : A) := map_smul _ _ _
      _ = algebraMap A Γ(Spec A, U) r := by
        rw [h1]
        change algebraMap A Γ(Spec A, U) r * 1 = _
        exact mul_one _
  have hr : (affineScalarSheafMap A r).app U (1 : Γ(Spec A, U)) =
      algebraMap A Γ(Spec A, U) r := by
    simpa only [scalarLinear, LinearMap.smulRight_apply, LinearMap.id_apply, one_smul, hr']
      using h
  rw [QuotientPair.unitSheaf_hom_apply, hr]
  rfl

/-- Canonical pullback identification retaining every original coordinate label. -/
def coordinatePullbackIso {X Y : Scheme.{u}} (f : Y ⟶ X) (n : ℕ) :
    (Scheme.Modules.pullback f).obj (coordinateFreeSheaf X n) ≅ coordinateFreeSheaf Y n :=
  SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom (CoordinateIndex.{u} n)

@[reassoc (attr := simp)]
theorem coordinatePullbackIso_generator {X Y : Scheme.{u}} (f : Y ⟶ X)
    {n : ℕ} (i : CoordinateIndex.{u} n) :
    (Scheme.Modules.pullback f).map (SheafOfModules.ιFree i) ≫
      (coordinatePullbackIso f n).hom =
    (QuotientPair.quotientPullbackUnitIso f).hom ≫ SheafOfModules.ιFree i :=
  SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom f.toRingCatSheafHom i

variable {A B : CommRingCat.{u}} (k : A ⟶ B)

/-- The structure-sheaf map transports a coefficient along the original
ring homomorphism on every inverse-image open. -/
theorem specMap_app_algebraMap (U : (Spec A).Opens) (r : A) :
    (Spec.map k).app U (algebraMap A Γ(Spec A, U) r) =
      algebraMap B Γ(Spec B, (Spec.map k) ⁻¹ᵁ U) (k r) :=
  StructureSheaf.toOpen_comp_comap_apply k.hom U r

/-- Scalar maps commute with the canonical unit-to-pushforward map. -/
theorem affineScalarSheafMap_pushforward (r : A) :
    affineScalarSheafMap A r ≫
      SheafOfModules.unitToPushforwardObjUnit (Spec.map k).toRingCatSheafHom =
    SheafOfModules.unitToPushforwardObjUnit (Spec.map k).toRingCatSheafHom ≫
      (Scheme.Modules.pushforward (Spec.map k)).map (affineScalarSheafMap B (k r)) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change (Spec.map k).app U ((affineScalarSheafMap A r).app U x) =
    (affineScalarSheafMap B (k r)).app ((Spec.map k) ⁻¹ᵁ U) ((Spec.map k).app U x)
  rw [affineScalarSheafMap_app, affineScalarSheafMap_app, map_mul,
    specMap_app_algebraMap]

/-- Geometric pullback of scalar multiplication, under the canonical
unit-sheaf comparison; no property of the ring homomorphism is required. -/
@[reassoc]
theorem affineScalarSheafMap_pullback (r : A) :
    (Scheme.Modules.pullback (Spec.map k)).map (affineScalarSheafMap A r) ≫
      (QuotientPair.quotientPullbackUnitIso (Spec.map k)).hom =
    (QuotientPair.quotientPullbackUnitIso (Spec.map k)).hom ≫
      affineScalarSheafMap B (k r) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map k)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  have hu : ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map k)).homEquiv _ _)
      (QuotientPair.quotientPullbackUnitIso (Spec.map k)).hom =
      SheafOfModules.unitToPushforwardObjUnit (Spec.map k).toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      (Spec.map k).toRingCatSheafHom
  rw [hu]
  exact affineScalarSheafMap_pushforward k r

end FlagVarieties.Foundations.QuotientCharts
