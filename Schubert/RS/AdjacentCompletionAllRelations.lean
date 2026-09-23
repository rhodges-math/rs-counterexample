import Schubert.RS.AdjacentCompletionRelations
import Schubert.RS.CompletionWeylRelations
import Schubert.RS.Representation.PolynomialWeylEndpoint
import Schubert.RS.Representation.PolynomialCompletionEvaluation

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000

variable {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
  (B : PolynomialRootStringBasis i.left i.right (compositionFlag (swapComposition u i)))
  (hu : u i.left<u i.right)

include hu

theorem PolynomialRootStringBasis.adjacentWeyl_endpoint :
    ∃ c : ℂ, c≠0 ∧ B.completedWeyl i.left_ne_right (B.adjacentHighest u i)=
      c • B.adjacentEndpoint u i := by
  exact B.completedWeyl_highest_endpoint i.left_ne_right
    { ne_zero := B.adjacentHighest_ne_zero u i
      lie_e := B.adjacentHighest_e u i hu
      lie_h := B.adjacentHighest_h u i hu }

/-- Every target Joseph–Polo root relation holds on the actual reflected
endpoint of the constructed completion. No presentation assumption is used. -/
theorem PolynomialRootStringBasis.adjacentEndpoint_jp (r : PositiveRoot n) :
    B.completedUpperEnveloping
      (compositionFlag_adjacent_raising_stable (swapComposition u i) i)
      (compositionFlag_radical_stable i (swapComposition u i))
      (rootOperator r^jpExponent u r) (B.adjacentEndpoint u i)=0 := by
  obtain ⟨s,hs,hη⟩ := B.adjacentWeyl_endpoint u i hu
  exact B.completedWeyl_jp_relations
    (compositionFlag_adjacent_raising_stable (swapComposition u i) i)
    (compositionFlag_radical_stable i (swapComposition u i)) u
    (B.adjacentHighest u i) (B.adjacentEndpoint u i) (B.adjacentHighest_jp u i)
    s hs hη (B.adjacentEndpoint_simple_jp u i hu) r

end
end Schubert.RS.Representation

