import RSCounterexample.FlagVarieties.Foundations.Schemes.PullbackQuotientTransport

/-!
# Pulling back comparisons of labelled quotient sheaves

A source-preserving comparison stays source preserving under arbitrary
scheme pullback. The composition comparison uses the pullback
functor and retains each of the original free-source labels.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u

theorem coordinatePullbackQuotient_map_target
    {X Y : Scheme.{u}} (f : X ⟶ Y) {n : ℕ} {M N : Y.Modules}
    (q : coordinateFreeSheaf Y n ⟶ M) (a : M ⟶ N) :
    coordinatePullbackQuotient f q ≫ (Scheme.Modules.pullback f).map a =
      coordinatePullbackQuotient f (q ≫ a) := by
  simp only [coordinatePullbackQuotient, Functor.map_comp, Category.assoc]

/-- Comparison after composition with any scheme morphism. -/
def coordinateQuotientComparisonPullback
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} {N : Y.Modules}
    (e : (Scheme.Modules.pullback g).obj M ≅ N) :
    (Scheme.Modules.pullback (f ≫ g)).obj M ≅ (Scheme.Modules.pullback f).obj N :=
  ((Scheme.Modules.pullbackComp f g).app M).symm ≪≫
    (Scheme.Modules.pullback f).mapIso e

@[reassoc]
theorem coordinateQuotientComparisonPullback_source
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {n : ℕ}
    {M : Z.Modules} {N : Y.Modules}
    (q : coordinateFreeSheaf Z n ⟶ M)
    (r : coordinateFreeSheaf Y n ⟶ N)
    (e : (Scheme.Modules.pullback g).obj M ≅ N)
    (he : coordinatePullbackQuotient g q ≫ e.hom = r) :
    coordinatePullbackQuotient (f ≫ g) q ≫
      (coordinateQuotientComparisonPullback f g e).hom =
      coordinatePullbackQuotient f r := by
  simp only [coordinateQuotientComparisonPullback, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_inv]
  rw [← Category.assoc, coordinatePullbackQuotient_comp,
    coordinatePullbackQuotient_map_target, he]

end FlagVarieties.Foundations.QuotientCharts
