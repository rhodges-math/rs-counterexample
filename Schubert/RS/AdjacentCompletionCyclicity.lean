import Schubert.RS.AdjacentCompletionGenerator
import Schubert.RS.ParabolicCompletionCyclicity
import Schubert.RS.Representation.PolynomialCompletionUpper

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

variable {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
  (B : PolynomialRootStringBasis i.left i.right (compositionFlag (swapComposition u i)))

/-- The actual completion of the sorted neighboring flag module is cyclic
under its constructed upper-enveloping action on the reflected endpoint. -/
theorem PolynomialRootStringBasis.adjacentEndpoint_cyclic (hu : u i.left<u i.right) :
    ∀ x : B.completedModule i.left_ne_right, ∃ a : Enveloping n,
      B.completedUpperEnveloping
        (compositionFlag_adjacent_raising_stable (swapComposition u i) i)
        (compositionFlag_radical_stable i (swapComposition u i)) a
          (B.adjacentEndpoint u i)=x := by
  let hE := compositionFlag_adjacent_raising_stable (swapComposition u i) i
  let hR := compositionFlag_radical_stable i (swapComposition u i)
  letI := B.completedRadicalLieRingModule hE hR
  letI := B.completedRadicalLieModule hE hR
  letI := B.completedRadical_isLieTower hE hR
  let ρ := polynomialSubmoduleEnveloping (compositionFlag (swapComposition u i))
    (positiveRoot_stable_of_simple_radical hE hR)
  have hc : ∀ m : compositionFlag (swapComposition u i), ∃ a : Enveloping n,
      ρ a (compositionFlagGenerator (swapComposition u i))=m := by
    intro m
    obtain ⟨a,ha⟩ := m.property
    exact ⟨a,Subtype.ext ha⟩
  exact parabolicCompletion_endpoint_cyclic i (B.isCompletion i.left_ne_right hE)
    ρ (compositionFlagGenerator (swapComposition u i)) (u i.right-u i.left) hc
    (B.completionBoundary_enveloping hE hR)
    (B.adjacentHighest_h u i hu) (B.adjacentHighest_e u i hu)

end
end Schubert.RS.Representation
