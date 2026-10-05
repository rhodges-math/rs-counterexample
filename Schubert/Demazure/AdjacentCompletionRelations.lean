import Schubert.Demazure.AdjacentCompletionCyclicity
import Schubert.Demazure.Sl2EndpointNilpotence
import Schubert.Demazure.FlagPresentationRelations
import Schubert.Demazure.ParabolicSimpleOperator

/-!
# Joseph–Polo relations at the adjacent highest vector

The Joseph–Polo root relations of `swapComposition u i` hold at the adjacent highest vector of the
completion (`adjacentHighest_josephPolo`), and the relation of the simple root of `i` for `u` holds
at the reflected endpoint (`adjacentEndpoint_simple_josephPolo`).
-/

open Schubert

namespace Demazure.FlagModule
noncomputable section
open FinPermutation
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

variable {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
  (B : PolynomialRootStringBasis i.left i.right (compositionFlag (swapComposition u i)))

theorem PolynomialRootStringBasis.adjacentHighest_josephPolo (r : PositiveRoot n) :
    B.completedUpperEnveloping
      (compositionFlag_adjacent_raising_stable (swapComposition u i) i)
      (compositionFlag_radical_stable i (swapComposition u i))
      (rootOperator r^josephPoloExponent (swapComposition u i) r) (B.adjacentHighest u i)=0 := by
  let hE := compositionFlag_adjacent_raising_stable (swapComposition u i) i
  let hR := compositionFlag_radical_stable i (swapComposition u i)
  change B.completedUpperEnveloping hE hR _
    (B.completionBoundary i.left_ne_right (compositionFlagGenerator (swapComposition u i)))=0
  rw [← B.completionBoundary_enveloping hE hR]
  have hz : polynomialSubmoduleEnveloping (compositionFlag (swapComposition u i))
      (positiveRoot_stable_of_simple_radical hE hR)
      (rootOperator r^josephPoloExponent (swapComposition u i) r)
      (compositionFlagGenerator (swapComposition u i))=0 := by
    apply Subtype.ext
    change polynomialEnveloping n (rootOperator r^josephPoloExponent (swapComposition u i) r)
      (extremalFlag (compositionShape (swapComposition u i))
        (compositionPermutation (swapComposition u i)))=0
    simpa only [composition_extremalWeight] using flagGenerator_josephPolo_relation
      (compositionShape (swapComposition u i)) (compositionPermutation (swapComposition u i)) r
  rw [hz,map_zero]

theorem PolynomialRootStringBasis.adjacentSimpleOperator :
    B.completedUpperEnveloping
      (compositionFlag_adjacent_raising_stable (swapComposition u i) i)
      (compositionFlag_radical_stable i (swapComposition u i))
          (rootOperator (adjacentPositiveRoot i))=
      LieModule.toEnd ℂ _ (B.completedModule i.left_ne_right)
        (sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right)) := by
  let hE := compositionFlag_adjacent_raising_stable (swapComposition u i) i
  let hR := compositionFlag_radical_stable i (swapComposition u i)
  let := B.completedRadicalLieRingModule hE hR
  let := B.completedRadicalLieModule hE hR
  let := B.completedRadical_isLieTower hE hR
  exact parabolicSimpleOperator i (B.completedModule i.left_ne_right)

/-- The remaining simple-root JP relation at the reflected endpoint follows
from the finite sl2 string. Non-simple relations require Weyl transport. -/
theorem PolynomialRootStringBasis.adjacentEndpoint_simple_josephPolo (hu : u i.left<u i.right) :
    B.completedUpperEnveloping
      (compositionFlag_adjacent_raising_stable (swapComposition u i) i)
      (compositionFlag_radical_stable i (swapComposition u i))
      (rootOperator (adjacentPositiveRoot i)^josephPoloExponent u (adjacentPositiveRoot i))
      (B.adjacentEndpoint u i)=0 := by
  rw [map_pow,B.adjacentSimpleOperator u i]
  exact highestVector_endpoint_e_end
    (sl2SubalgebraTriple (polynomialSl2Triple i.left i.right i.left_ne_right))
    (B.adjacentHighest_h u i hu) (B.adjacentHighest_e u i hu)

end
end Demazure.FlagModule
