import Schubert.FlagVarieties.Foundations.Flags.CoordinateBaseChange
import Schubert.FlagVarieties.Foundations.Flags.BaseChangeImages

/-!
# Coordinate base change and the tensor-image description

The coordinate quotient has precisely the tensor image of the original
kernel. This comparison uses right exactness, so it also holds for nonflat
scalar extension.
-/

namespace FlagVarieties.Foundations.QuotientCharts

open TensorProduct

variable {R : Type*} [CommRing R] (B : Type*) [CommRing B] [Algebra R B]
  {n d : ℕ}

theorem coordinateGrassmannianBaseChange_submodule
    (P : Module.Grassmannian R (Fin n → R) d) :
    (coordinateGrassmannianBaseChange B P).toSubmodule =
      (P.toSubmodule.baseChange B).map
        (TensorProduct.piScalarRight R B B (Fin n)).toLinearMap := by
  change LinearMap.ker ((P.toSubmodule.mkQ.baseChange B).comp
    (TensorProduct.piScalarRight R B B (Fin n)).symm.toLinearMap) = _
  rw [LinearMap.ker_comp, baseChange_mkQ_ker]
  exact ((P.toSubmodule.baseChange B).map_equiv_eq_comap_symm
    (TensorProduct.piScalarRight R B B (Fin n))).symm

end FlagVarieties.Foundations.QuotientCharts
