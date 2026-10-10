import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedSheafBaseChangeScalar
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedPresentationSheaf
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! The constant matrix action on the labelled finite free sheaf. -/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory

universe u
variable (R : Type u) [CommRing R] {n : ℕ}

/-- Sheafify the original coordinate matrix over `Spec R`, preserving the
standard `Fin n` labels through `coordinateTildeFreeIso`. -/
def constantMatrixSpecIso (L : Matrix (Fin n) (Fin n) R) (hL : IsUnit L) :
    coordinateFreeSheaf (Spec (CommRingCat.of R)) n ≅
      coordinateFreeSheaf (Spec (CommRingCat.of R)) n :=
  (coordinateTildeFreeIso (CommRingCat.of R) n).symm ≪≫
    (tilde.functor (CommRingCat.of R)).mapIso
      (L.toLinearEquiv' hL.invertible).toModuleIso ≪≫
        coordinateTildeFreeIso (CommRingCat.of R) n

/-- Pull the constant matrix action to any `R`-scheme, using the
canonical labelled free-source comparison on that scheme. -/
def constantMatrixSheafIso {X : Scheme.{u}}
    (b : X ⟶ Spec (CommRingCat.of R))
    (L : Matrix (Fin n) (Fin n) R) (hL : IsUnit L) :
    coordinateFreeSheaf X n ≅ coordinateFreeSheaf X n :=
  (coordinatePullbackIso b n).symm ≪≫
    (Scheme.Modules.pullback b).mapIso (constantMatrixSpecIso R L hL) ≪≫
      coordinatePullbackIso b n

end FlagVarieties.Foundations.QuotientCharts
