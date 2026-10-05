import Schubert.FlagVarieties.Foundations.Schemes.SelectedFlagChartSchemeProjections
import Schubert.FlagVarieties.Foundations.Schemes.SelectedUniversalMorphismUniquenessAffine

/-! # The universal quotient at each step of the glued flag scheme -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] (n : ℕ)

/-- Pull back the original Grassmannian universal quotient target. -/
def selectedFlagUniversalTarget (j : Fin (n+1)) : (selectedFlagChartScheme R n).Modules :=
  (Scheme.Modules.pullback (selectedFlagChartSchemeStep R n j)).obj
    (selectedUniversalQuotientSheaf R n (n-j.val))

/-- The original labelled rank-n source is retained at every step. -/
def selectedFlagUniversalQuotient (j : Fin (n+1)) :
    coordinateFreeSheaf (selectedFlagChartScheme R n) n ⟶ selectedFlagUniversalTarget R n j :=
  coordinatePullbackQuotient (selectedFlagChartSchemeStep R n j)
    (selectedUniversalQuotient R n (n-j.val))

instance selectedFlagUniversalQuotient_epi (j : Fin (n+1)) :
    Epi (selectedFlagUniversalQuotient R n j) := by
  unfold selectedFlagUniversalQuotient
  infer_instance

theorem selectedFlagUniversalTarget_local_frames (j : Fin (n+1))
    (x : selectedFlagChartScheme R n) :
    ∃ U : (selectedFlagChartScheme R n).Opens, x ∈ U ∧
      Nonempty ((selectedFlagUniversalTarget R n j).over U ≅
        SheafOfModules.free (R := (selectedFlagChartScheme R n).ringCatSheaf.over U)
          (CoordinateIndex.{u} (n-j.val))) :=
  selectedUniversalQuotient_pullback_over_frames R n (n-j.val)
    (selectedFlagChartSchemeStep R n j) x

end FlagVarieties.Foundations.QuotientCharts
