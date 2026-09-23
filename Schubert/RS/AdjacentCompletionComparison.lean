import Schubert.RS.AdjacentCompletionGenerator
import Schubert.RS.AdjacentGeneratorScalar
import Schubert.RS.PolynomialLoweringComparison

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

variable {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
  (B : PolynomialRootStringBasis i.left i.right (compositionFlag (swapComposition u i)))
  (f : B.completedModule i.left_ne_right →ₗ[ℂ] MatrixPolynomial n)
  (hb : ∀ p : compositionFlag (swapComposition u i),
    f (B.completionBoundary i.left_ne_right p)=p.val)
  (hf : ∀ x, f ⁅sl2LoweringElement (polynomialSl2Triple i.left i.right i.left_ne_right),x⁆=
    matrixUnitDerivation i.right i.left (f x))

include hb hf

theorem PolynomialRootStringBasis.adjacentEndpoint_evaluation :
    f (B.adjacentEndpoint u i)=
      derivationIter (matrixUnitDerivation i.right i.left) (u i.right-u i.left)
        (compositionFlagGenerator (swapComposition u i)).val := by
  change f (primitiveStringVector _ (B.adjacentHighest u i) _)=_
  rw [polynomial_string_comparison f _ i.right i.left hf]
  change derivationIter _ _ (f (B.completionBoundary i.left_ne_right
    (compositionFlagGenerator (swapComposition u i))))=_
  rw [hb]

theorem PolynomialRootStringBasis.adjacentEndpoint_evaluation_scalar (hu : u i.left<u i.right) :
    ∃ c : ℂ, c≠0 ∧ (compositionFlagGenerator u).val=c • f (B.adjacentEndpoint u i) := by
  rw [B.adjacentEndpoint_evaluation u i f hb hf]
  exact compositionFlagGenerator_reverse_scalar u i hu

end
end Schubert.RS.Representation
