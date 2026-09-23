import Schubert.RS.JosephPolo.CompletionComparison
import Schubert.RS.JosephPolo.CyclicScalar
import Schubert.RS.AdjacentCompletionEvaluation
import Schubert.RS.JosephPolo.Dominant
import Schubert.RS.SortingIndependence

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance 100] LieRing.ofAssociativeRing
set_option Elab.async false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 200000

variable {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
  (hu : u i.left < u i.right)
  (B : PolynomialRootStringBasis i.left i.right (compositionFlag (swapComposition u i)))

/-- The two comparisons compose to the canonical polynomial map, with the
single nonzero normalization scalar already determined on the generator. -/
theorem presentation_adjacent_evaluation_scalar :
    letI := B.completedUpperModule
      (compositionFlag_adjacent_raising_stable (swapComposition u i) i)
      (compositionFlag_radical_stable i (swapComposition u i))
    ∃ c : ℂ, c ≠ 0 ∧ ∀ q : PresentationQuotient u,
      compositionPresentationMap u q =
        c • B.adjacentEvaluation u i hu (presentationToAdjacentCompletion u i hu B q) := by
  let hE := compositionFlag_adjacent_raising_stable (swapComposition u i) i
  let hR := compositionFlag_radical_stable i (swapComposition u i)
  letI := B.completedUpperModule hE hR
  obtain ⟨c,hc,hgen⟩ := B.adjacentEvaluation_endpoint_scalar u i hu
  refine ⟨c,hc,?_⟩
  let f := presentationToAdjacentCompletion u i hu B
  let e := B.adjacentEvaluationU u i hu
  have hf : f (presentationGenerator u) = B.adjacentEndpoint u i :=
    presentationLift_generator u _ _
  have he : compositionFlagGenerator u = c • e (f (presentationGenerator u)) :=
    hgen.trans (congrArg (fun x => c • e x) hf.symm)
  exact presentation_maps_scalar u f e c he

/-- The adjacent Joseph-Polo presentation property is equivalent to
injectivity of polynomial evaluation under the stated hypotheses. -/
theorem compositionFlagJosephPolo_iff_adjacent_evaluation_injective
    (hJP : CompositionFlagJosephPolo (swapComposition u i)) :
    CompositionFlagJosephPolo u ↔ Function.Injective (B.adjacentEvaluation u i hu) := by
  let hE := compositionFlag_adjacent_raising_stable (swapComposition u i) i
  let hR := compositionFlag_radical_stable i (swapComposition u i)
  letI := B.completedUpperModule hE hR
  let f := presentationToAdjacentCompletion u i hu B
  obtain ⟨c,hc,hmap⟩ := presentation_adjacent_evaluation_scalar u i hu B
  have hf : Function.Bijective f := presentationToAdjacentCompletion_bijective u i hu B hJP
  rw [compositionFlagJosephPolo_iff_injective]
  constructor
  · intro h x y hxy
    obtain ⟨p,rfl⟩ := hf.2 x
    obtain ⟨q,rfl⟩ := hf.2 y
    apply congrArg f
    apply h
    rw [hmap,hmap]
    exact congrArg (c • ·) hxy
  · intro h p q hpq
    apply hf.1
    apply h
    apply (smul_right_injective _ hc)
    exact (hmap p).symm.trans (hpq.trans (hmap q))

/-- A terminating induction from injectivity of the adjacent polynomial
evaluation maps. -/
theorem compositionFlagJosephPolo_of_evaluation_witnesses
    (hK2 : ∀ u : Composition n, ¬Antitone u →
      ∃ (i : AdjacentPosition n) (hu : u i.left < u i.right)
        (B : PolynomialRootStringBasis i.left i.right (compositionFlag (swapComposition u i))),
        Function.Injective (B.adjacentEvaluation u i hu)) :
    ∀ u : Composition n, CompositionFlagJosephPolo u := by
  intro u
  induction u using (measure sortingMeasure).wf.induction with
  | h u ih =>
    by_cases hu : Antitone u
    · exact compositionFlagJosephPolo_of_antitone u hu
    · obtain ⟨i,hi,B,hB⟩ := hK2 u hu
      exact (compositionFlagJosephPolo_iff_adjacent_evaluation_injective u i hi B
        (ih _ (sortingMeasure_swap_lt u i hi))).mpr hB

end
end Schubert.RS.Representation
