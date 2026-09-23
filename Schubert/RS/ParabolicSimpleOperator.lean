import Schubert.RS.ParabolicCyclicOrbit

namespace Schubert.RS.Representation
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
      LieModule.toEnd ℂ _ X (sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right)) := by
  have hr : rootOperator (adjacentPositiveRoot i)=
      UniversalEnvelopingAlgebra.ι ℂ (rootBasis n (adjacentPositiveRoot i)) := by
    rw [rootBasis_apply]
    rfl
  rw [hr,parabolicUpperEnveloping_ι]
  exact LinearMap.ext (parabolicUpperLie_adjacent i X)

end
end Schubert.RS.Representation
