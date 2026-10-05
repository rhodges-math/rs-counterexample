import Schubert.FlagVarieties.Foundations.Schemes.SelectedChartSchemeStructure
import Schubert.FlagVarieties.Foundations.Schemes.CoordinateSheafGenerators
import Schubert.FlagVarieties.Foundations.Schemes.QuotientLineSheafPullback

/-!
# Local universal quotients on the selected-chart scheme

Each chart range is an open subscheme, canonically isomorphic to
its original polynomial spectrum. The identity polynomial evaluation gives
a split quotient there. Pulling it back along that isomorphism
constructs the local quotient of the global coordinate free sheaf.
Compatibility on overlaps is proved in `Schemes/SelectedUniversalOverlap.lean`
and `Schemes/SelectedUniversalTransition.lean`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory

universe u

/-- Restriction of the original coordinate free sheaf, with its labels retained. -/
def coordinateRestrictFreeIso {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    (coordinateFreeSheaf X n).restrict j ≅ coordinateFreeSheaf Y n := by
  let : CategoryTheory.Limits.PreservesColimitsOfSize.{u,u}
      (Scheme.Modules.restrictFunctor j) := inferInstance
  exact (SheafOfModules.mapFreeIso (Scheme.Modules.restrictFunctor j)
    (CoordinateIndex.{u} n) (Scheme.Modules.restrictUnitIso j).symm).symm

/-- Canonical pullback of the original coordinate free sheaf. -/
def coordinatePullbackFreeIso {X Y : Scheme.{u}} (j : Y ⟶ X) (n : ℕ) :
    (Scheme.Modules.pullback j).obj (coordinateFreeSheaf X n) ≅ coordinateFreeSheaf Y n :=
  SheafOfModules.pullbackObjFreeIso j.toRingCatSheafHom (CoordinateIndex.{u} n)

variable (R : Type u) [CommRing R] (n d : ℕ)

/-- The range open of the selected-coordinate chart. -/
def selectedUniversalOpen (a : Fin d ↪ Fin n) : (selectedChartScheme R n d).Opens :=
  (selectedChartSchemeChart R n d a).opensRange

/-- The original polynomial chart is canonically isomorphic to its range open. -/
def selectedUniversalOpenIso (a : Fin d ↪ Fin n) :
    Spec (CommRingCat.of (MvPolynomial (Fin d × Fin (n - d)) R)) ≅
      (selectedUniversalOpen R n d a).toScheme :=
  (selectedChartSchemeChart R n d a).isoOpensRange

theorem selectedUniversalOpen_cover (x : selectedChartScheme R n d) :
    ∃ a : Fin d ↪ Fin n, x ∈ selectedUniversalOpen R n d a := by
  obtain ⟨a, y, hy⟩ := selectedChartSchemeChart_jointly_surjective R n d x
  exact ⟨a, y, hy⟩

/-- The local rank-d target, on an open subscheme of the glued scheme. -/
abbrev selectedUniversalLocalTarget (a : Fin d ↪ Fin n) :
    (selectedUniversalOpen R n d a).toScheme.Modules :=
  coordinateFreeSheaf (selectedUniversalOpen R n d a).toScheme d

/-- The identity-evaluated matrix chart quotient, transported to its range open. -/
def selectedUniversalLocalQuotient (a : Fin d ↪ Fin n) :
    (coordinateFreeSheaf (selectedChartScheme R n d) n).restrict
        (selectedUniversalOpen R n d a).ι ⟶ selectedUniversalLocalTarget R n d a :=
  (coordinateRestrictFreeIso (selectedUniversalOpen R n d a).ι n).hom ≫
    (coordinatePullbackFreeIso (selectedUniversalOpenIso R n d a).inv n).inv ≫
      (Scheme.Modules.pullback (selectedUniversalOpenIso R n d a).inv).map
        (selectedPresentationSheafMap R (CommRingCat.of (MvPolynomial (Fin d × Fin (n - d)) R))
          a (AlgHom.id R _)) ≫
        (coordinatePullbackFreeIso (selectedUniversalOpenIso R n d a).inv d).hom

/-- No local quotient epimorphism is supplied as an input. -/
instance selectedUniversalLocalQuotient_epi (a : Fin d ↪ Fin n) :
    Epi (selectedUniversalLocalQuotient R n d a) := by
  unfold selectedUniversalLocalQuotient
  infer_instance

end FlagVarieties.Foundations.QuotientCharts
