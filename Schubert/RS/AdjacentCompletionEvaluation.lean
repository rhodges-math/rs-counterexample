import Schubert.RS.AdjacentCompletionComparison
import Schubert.RS.CompletionEvaluationLinear

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance 100] LieRing.ofAssociativeRing
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 200000

theorem compositionFlag_adjacent_lowering_stable {n : ℕ} (u : Composition n)
    (i : AdjacentPosition n) (hu : u i.left<u i.right)
    (p : MatrixPolynomial n) (hp : p∈compositionFlag u) :
    matrixUnitDerivation i.right i.left p∈compositionFlag u :=
  adjacent_lowering_flagDemazure_stable (compositionShape u) (compositionPermutation u) i
    (by simpa only [composition_extremalWeight] using hu) hp

variable {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
  (B : PolynomialRootStringBasis i.left i.right (compositionFlag (swapComposition u i)))
  (hu : u i.left<u i.right)

def PolynomialRootStringBasis.adjacentEvaluation :
    B.completedModule i.left_ne_right →ₗ[ℂ] compositionFlag u :=
  B.completionEvaluationLinear
    (compositionFlag_adjacent_raising_stable (swapComposition u i) i)
    (compositionFlag_adjacent_raising_stable u i)
    (compositionFlag_adjacent_lowering_stable u i hu)
    (compositionFlag_adjacent_le u i hu)
theorem PolynomialRootStringBasis.adjacentEvaluation_boundary
    (p : compositionFlag (swapComposition u i)) :
    (B.adjacentEvaluation u i hu (B.completionBoundary i.left_ne_right p)).val=p.val :=
  B.completionEvaluationLinear_boundary
    (compositionFlag_adjacent_raising_stable (swapComposition u i) i)
    (compositionFlag_adjacent_raising_stable u i)
    (compositionFlag_adjacent_lowering_stable u i hu)
    (compositionFlag_adjacent_le u i hu) p


theorem PolynomialRootStringBasis.adjacentEvaluation_lowering (x : B.completedModule i.left_ne_right) :
    (B.adjacentEvaluation u i hu
      ⁅sl2LoweringElement (polynomialSl2Triple i.left i.right i.left_ne_right),x⁆).val=
      matrixUnitDerivation i.right i.left (B.adjacentEvaluation u i hu x).val :=
  B.completionEvaluationLinear_lowering
    (compositionFlag_adjacent_raising_stable (swapComposition u i) i)
    (compositionFlag_adjacent_raising_stable u i)
    (compositionFlag_adjacent_lowering_stable u i hu)
    (compositionFlag_adjacent_le u i hu) x
theorem PolynomialRootStringBasis.adjacentEvaluation_enveloping (a : Enveloping n)
    (x : B.completedModule i.left_ne_right) :
    (B.adjacentEvaluation u i hu
      (B.completedUpperEnveloping
        (compositionFlag_adjacent_raising_stable (swapComposition u i) i)
        (compositionFlag_radical_stable i (swapComposition u i)) a x)).val=
      polynomialEnveloping n a (B.adjacentEvaluation u i hu x).val :=
  B.completionEvaluation_enveloping_val
    (compositionFlag_adjacent_raising_stable (swapComposition u i) i)
    (compositionFlag_radical_stable i (swapComposition u i))
    (compositionFlag_adjacent_raising_stable u i)
    (compositionFlag_adjacent_lowering_stable u i hu)
    (compositionFlag_radical_stable i u) (compositionFlag_adjacent_le u i hu) a x

/-- Evaluation into the flag module with its upper-enveloping action. -/
def PolynomialRootStringBasis.adjacentEvaluationU :
    letI := B.completedUpperModule
      (compositionFlag_adjacent_raising_stable (swapComposition u i) i)
      (compositionFlag_radical_stable i (swapComposition u i))
    B.completedModule i.left_ne_right →ₗ[Enveloping n] compositionFlag u :=
  letI := B.completedUpperModule
    (compositionFlag_adjacent_raising_stable (swapComposition u i) i)
    (compositionFlag_radical_stable i (swapComposition u i))
  { toFun := B.adjacentEvaluation u i hu
    map_add' := (B.adjacentEvaluation u i hu).map_add
    map_smul' := fun a x => Subtype.ext (B.adjacentEvaluation_enveloping u i hu a x) }

theorem PolynomialRootStringBasis.adjacentEvaluation_endpoint_scalar :
    ∃ c : ℂ, c≠0 ∧ compositionFlagGenerator u=
      c • B.adjacentEvaluation u i hu (B.adjacentEndpoint u i) := by
  obtain ⟨c,hc,he⟩ := B.adjacentEndpoint_evaluation_scalar u i
    ((compositionFlag u).subtype.comp (B.adjacentEvaluation u i hu))
    (B.adjacentEvaluation_boundary u i hu) (B.adjacentEvaluation_lowering u i hu) hu
  exact ⟨c,hc,Subtype.ext he⟩

end
end Schubert.RS.Representation


