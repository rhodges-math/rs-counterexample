import Schubert.FlagVarieties.Foundations.Schemes.CoordinateQuotientCoverDescent
import Schubert.FlagVarieties.Foundations.Schemes.PullbackQuotientTransport

/-!
# Recovering a global quotient from local classifying maps

If a scheme morphism has the prescribed local classifying maps,
its universal pullback recovers the original global quotient. Compatibility
of the sheaf comparisons follows from their common epimorphic source.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u v
variable (R : Type u) [CommRing R] {X : Scheme.{u}} {n d : ℕ} {M : X.Modules}
  (q : coordinateFreeSheaf X n ⟶ M) [Epi q] (C : X.OpenCover.{v})
  (f : ∀ i, C.X i ⟶ selectedChartScheme R n d)
  (e : ∀ i, (Scheme.Modules.pullback (f i)).obj (selectedUniversalQuotientSheaf R n d) ≅
    (Scheme.Modules.pullback (C.f i)).obj M)
  (he : ∀ i, coordinatePullbackQuotient (f i) (selectedUniversalQuotient R n d) ≫
    (e i).hom = coordinatePullbackQuotient (C.f i) q)
  (F : X ⟶ selectedChartScheme R n d) (hF : ∀ i, C.f i ≫ F = f i)

/-- The local comparison after restricting the global classifying morphism. -/
def selectedUniversalQuotientLocalComparison (i : C.I₀) :
    (Scheme.Modules.pullback (C.f i)).obj
        ((Scheme.Modules.pullback F).obj (selectedUniversalQuotientSheaf R n d)) ≅
      (Scheme.Modules.pullback (C.f i)).obj M :=
  (Scheme.Modules.pullbackComp (C.f i) F).app (selectedUniversalQuotientSheaf R n d) ≪≫
    (Scheme.Modules.pullbackCongr (hF i)).app (selectedUniversalQuotientSheaf R n d) ≪≫ e i

include he

omit [Epi q] in
theorem selectedUniversalQuotientLocalComparison_source (i : C.I₀) :
    coordinatePullbackQuotient (C.f i)
        (coordinatePullbackQuotient F (selectedUniversalQuotient R n d)) ≫
      (selectedUniversalQuotientLocalComparison R C f e F hF i).hom =
        coordinatePullbackQuotient (C.f i) q :=
  coordinatePullbackQuotient_transport (C.f i) F (hF i)
    (selectedUniversalQuotient R n d) (e i) (coordinatePullbackQuotient (C.f i) q) (he i)

/-- Global recovery of the target, descended from any such local classifying maps. -/
def selectedUniversalQuotientIsoOfLocal :
    (Scheme.Modules.pullback F).obj (selectedUniversalQuotientSheaf R n d) ≅ M :=
  coordinateQuotientIsoOfCover C
    (coordinatePullbackQuotient F (selectedUniversalQuotient R n d)) q
    (selectedUniversalQuotientLocalComparison R C f e F hF)
    (selectedUniversalQuotientLocalComparison_source R q C f e he F hF)

@[reassoc]
theorem selectedUniversalQuotientIsoOfLocal_source :
    coordinatePullbackQuotient F (selectedUniversalQuotient R n d) ≫
      (selectedUniversalQuotientIsoOfLocal R q C f e he F hF).hom = q :=
  coordinateQuotientIsoOfCover_source C _ q _ _

end FlagVarieties.Foundations.QuotientCharts
