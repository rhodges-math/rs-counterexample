import Schubert.FlagVarieties.Foundations.Schemes.SelectedUniversalAffineCover

/-!
# Source preservation through composite pullback comparisons

The comparison is the pullback composition isomorphism, followed by
transport along an equality of scheme maps and a given source-preserving
target comparison. The target sheaf is arbitrary.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u

theorem coordinatePullbackQuotient_transport
    {X Y Z : Scheme.{u}} {n : ℕ} (f : X ⟶ Y) (g : Y ⟶ Z)
    {h : X ⟶ Z} (w : f ≫ g = h) {M : Z.Modules}
    (q : coordinateFreeSheaf Z n ⟶ M) {N : X.Modules}
    (e : (Scheme.Modules.pullback h).obj M ≅ N)
    (t : coordinateFreeSheaf X n ⟶ N)
    (he : coordinatePullbackQuotient h q ≫ e.hom = t) :
    coordinatePullbackQuotient f (coordinatePullbackQuotient g q) ≫
      (((Scheme.Modules.pullbackComp f g).app M ≪≫
        (Scheme.Modules.pullbackCongr w).app M ≪≫ e).hom) = t := by
  simp only [Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, ← Category.assoc,
    coordinatePullbackQuotient_comp_hom, coordinatePullbackQuotient_congr]
  exact he

end FlagVarieties.Foundations.QuotientCharts
