import Schubert.FlagVarieties.Foundations.Schemes.SelectedFlagMatrixAction
import Schubert.FlagVarieties.Foundations.Schemes.ConstantMatrixSheafNaturality

/-! The constant matrix flag action respects arbitrary geometric pullback. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] {X Y : Scheme.{u}} {n : ℕ}
  (b : X ⟶ Spec (.of R)) (f : Y ⟶ X)
  (L : Matrix (Fin n) (Fin n) R) (hL : IsUnit L)

theorem coordinatePullbackQuotient_constantMatrix_inv
    {M : X.Modules} (q : coordinateFreeSheaf X n ⟶ M) :
    coordinatePullbackQuotient f ((constantMatrixSheafIso R b L hL).inv ≫ q) =
      (constantMatrixSheafIso R (f ≫ b) L hL).inv ≫
        coordinatePullbackQuotient f q := by
  have hh := congrArg (fun t =>
      (Scheme.Modules.pullback f).map (constantMatrixSheafIso R b L hL).inv ≫
        t ≫ (constantMatrixSheafIso R (f ≫ b) L hL).inv)
    (constantMatrixSheafIso_pullback R b f L hL)
  simp only [Category.assoc, Iso.inv_hom_id_map_assoc,
    Iso.hom_inv_id, Category.comp_id] at hh
  have hi : (coordinatePullbackIso f n).inv ≫
      (Scheme.Modules.pullback f).map (constantMatrixSheafIso R b L hL).inv =
    (constantMatrixSheafIso R (f ≫ b) L hL).inv ≫ (coordinatePullbackIso f n).inv := by
    apply (cancel_mono (coordinatePullbackIso f n).hom).mp
    simp only [Category.assoc]
    rw [← hh]
    simp
  simp only [coordinatePullbackQuotient, Functor.map_comp]
  simp only [coordinatePullbackIso_eq] at hi
  rw [← Category.assoc, hi, Category.assoc]

theorem QuotientFlagFamily.matrixTransport_pullback
    (F : QuotientFlagFamily X n) :
    (F.matrixTransport R b L hL).pullback f =
      (F.pullback f).matrixTransport R (f ≫ b) L hL := by
  have hq : (fun j => coordinatePullbackQuotient f
      ((constantMatrixSheafIso R b L hL).inv ≫ F.quotient j)) =
      (fun j => (constantMatrixSheafIso R (f ≫ b) L hL).inv ≫
        coordinatePullbackQuotient f (F.quotient j)) := by
    funext j
    exact coordinatePullbackQuotient_constantMatrix_inv R b f L hL (F.quotient j)
  simp only [QuotientFlagFamily.matrixTransport, QuotientFlagFamily.pullback]
  congr 1

theorem selectedFlagMatrixAction_pullback_transport
    (p : X ⟶ selectedFlagChartScheme R n) :
    p ≫ selectedFlagMatrixAction R L hL =
      globalQuotientFlagMorphism R (p ≫ selectedFlagChartSchemeToSpec R n)
        (((selectedFlagUniversalFamily R n).pullback p).matrixTransport R
          (p ≫ selectedFlagChartSchemeToSpec R n) L hL) := by
  rw [selectedFlagMatrixAction_pullback, QuotientFlagFamily.matrixTransport_pullback]

end FlagVarieties.Foundations.QuotientCharts
