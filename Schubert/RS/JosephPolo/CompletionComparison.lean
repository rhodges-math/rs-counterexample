import Schubert.RS.JosephPolo.CompletionUpper
import Schubert.RS.JosephPolo.CompletionGenerator
import Schubert.RS.AdjacentCompletionAllRelations
import Schubert.RS.AdjacentCompletionCyclicity

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 600000

variable {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
  (hu : u i.left<u i.right)
  (B : PolynomialRootStringBasis i.left i.right (compositionFlag (swapComposition u i)))

/-- The canonical presentation-to-completion map, with the reflected
endpoint as cyclic generator. Its construction uses no JP assumption. -/
def presentationToAdjacentCompletion :
    letI := B.completedUpperModule
      (compositionFlag_adjacent_raising_stable (swapComposition u i) i)
      (compositionFlag_radical_stable i (swapComposition u i))
    PresentationQuotient u →ₗ[Enveloping n] B.completedModule i.left_ne_right :=
  letI := B.completedUpperModule
    (compositionFlag_adjacent_raising_stable (swapComposition u i) i)
    (compositionFlag_radical_stable i (swapComposition u i))
  presentationLift u (B.adjacentEndpoint u i) (B.adjacentEndpoint_jp u i hu)

theorem presentationToAdjacentCompletion_surjective :
    letI := B.completedUpperModule
      (compositionFlag_adjacent_raising_stable (swapComposition u i) i)
      (compositionFlag_radical_stable i (swapComposition u i))
    Function.Surjective (presentationToAdjacentCompletion u i hu B) := by
  letI := B.completedUpperModule
    (compositionFlag_adjacent_raising_stable (swapComposition u i) i)
    (compositionFlag_radical_stable i (swapComposition u i))
  exact presentationLift_surjective u (B.adjacentEndpoint u i)
    (B.adjacentEndpoint_jp u i hu) (B.adjacentEndpoint_cyclic u i hu)

variable (hJP : CompositionFlagJosephPolo (swapComposition u i))

theorem adjacentCompletionToPresentation_surjective :
    letI := presentationSl2LieRingModule u i hu.le
    letI := presentationSl2LieModule u i hu.le
    Function.Surjective (adjacentCompletionToPresentation u i hu.le hJP B) := by
  letI := presentationSl2LieRingModule u i hu.le
  letI := presentationSl2LieModule u i hu.le
  obtain ⟨z,hz⟩ := adjacentCompletionToPresentation_generator_mem u i hu.le hJP B
  intro x
  obtain ⟨a,rfl⟩ := presentation_is_cyclic u x
  refine ⟨B.completedUpperEnveloping
    (compositionFlag_adjacent_raising_stable (swapComposition u i) i)
    (compositionFlag_radical_stable i (swapComposition u i)) a z,?_⟩
  rw [adjacentCompletionToPresentation_enveloping]
  exact congrArg (fun q : PresentationQuotient u => a • q) hz

include hJP in
/-- The universal presentation and finite root completion are isomorphic
under the Joseph-Polo hypothesis for the smaller composition. -/
theorem presentationToAdjacentCompletion_bijective :
    letI := B.completedUpperModule
      (compositionFlag_adjacent_raising_stable (swapComposition u i) i)
      (compositionFlag_radical_stable i (swapComposition u i))
    Function.Bijective (presentationToAdjacentCompletion u i hu B) := by
  let hE := compositionFlag_adjacent_raising_stable (swapComposition u i) i
  let hR := compositionFlag_radical_stable i (swapComposition u i)
  letI := B.completedUpperModule hE hR
  letI := B.completedUpperTower hE hR
  letI := presentationSl2LieRingModule u i hu.le
  letI := presentationSl2LieModule u i hu.le
  letI := presentation_finite u
  let f := (presentationToAdjacentCompletion u i hu B).restrictScalars ℂ
  let g := (adjacentCompletionToPresentation u i hu.le hJP B).toLinearMap
  have hf : Function.Surjective f := presentationToAdjacentCompletion_surjective u i hu B
  have hg : Function.Surjective g := adjacentCompletionToPresentation_surjective u i hu B hJP
  have hc : Function.Injective (g.comp f) := Module.End.injective_of_surjective ℂ _ (hg.comp hf)
  exact ⟨fun x y hxy => hc (congrArg g hxy),hf⟩

end
end Schubert.RS.Representation
