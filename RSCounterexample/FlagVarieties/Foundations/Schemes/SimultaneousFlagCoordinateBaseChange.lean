import RSCounterexample.FlagVarieties.Foundations.Schemes.SimultaneousFlagCoordinateCoverLocal

/-!
# Base change of the original coordinate flag

The steps are the coordinate scalar extensions of the given flag
quotients. Nesting and endpoints follow from tensor-image functoriality;
there is no substituted rank-defined flag.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

open TensorProduct

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  {n : ℕ} (F : RingFlag A (Fin n → A) n)

/-- The given coordinate flag after arbitrary extension of coefficients. -/
def coordinateRingFlagBaseChange : RingFlag B (Fin n → B) n where
  step j := coordinateGrassmannianBaseChange B (F.step j)
  step_mono := by
    intro i j hij
    change (coordinateGrassmannianBaseChange B (F.step i)).toSubmodule ≤
      (coordinateGrassmannianBaseChange B (F.step j)).toSubmodule
    rw [coordinateGrassmannianBaseChange_submodule,
      coordinateGrassmannianBaseChange_submodule]
    exact Submodule.map_mono (Submodule.baseChange_mono (A := B) (F.step_mono hij))
  step_zero := by
    rw [coordinateGrassmannianBaseChange_submodule, F.step_zero,
      Submodule.baseChange_bot, Submodule.map_bot]
  step_last := by
    rw [coordinateGrassmannianBaseChange_submodule, F.step_last,
      Submodule.baseChange_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (TensorProduct.piScalarRight A B B (Fin n)).surjective

@[simp] theorem coordinateRingFlagBaseChange_step (j : Fin (n + 1)) :
    (coordinateRingFlagBaseChange (B := B) F).step j =
      coordinateGrassmannianBaseChange B (F.step j) := rfl

end FlagVarieties.Foundations.QuotientCharts
