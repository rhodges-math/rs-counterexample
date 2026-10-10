import RSCounterexample.Demazure.ParabolicCyclicOrbit

/-!
# The simple root operator in the parabolic action

In the parabolic upper action on a module over the `sl₂` of `i` and the radical, the operator of the
simple root of `i` is the raising element (`parabolicSimpleOperator`).
-/

open Schubert

namespace Demazure.FlagModule
noncomputable section
open FinPermutation
attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ} (i : AdjacentPosition n) (X : Type*) [AddCommGroup X] [Module ℂ X]
  [LieRingModule ((polynomialSl2Triple i.left i.right i.left_ne_right).toLieSubalgebra ℂ) X]
  [LieModule ℂ ((polynomialSl2Triple i.left i.right i.left_ne_right).toLieSubalgebra ℂ) X]
  [LieRingModule (radicalEndLie i) X] [LieModule ℂ (radicalEndLie i) X]
  [IsLieTower ((polynomialSl2Triple i.left i.right i.left_ne_right).toLieSubalgebra ℂ)
    (radicalEndLie i) X]

theorem parabolicSimpleOperator :
    parabolicUpperEnveloping i X (rootOperator (adjacentPositiveRoot i))=
      LieModule.toEnd ℂ _ X
          (sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right)) := by
  have hr : rootOperator (adjacentPositiveRoot i)=
      UniversalEnvelopingAlgebra.ι ℂ (rootBasis n (adjacentPositiveRoot i)) := by
    rw [rootBasis_apply]
    rfl
  rw [hr,parabolicUpperEnveloping_ι]
  exact LinearMap.ext (parabolicUpperLie_adjacent i X)

end
end Demazure.FlagModule
