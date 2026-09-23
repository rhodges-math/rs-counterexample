import Schubert.RS.PolynomialCompletionCharacter
import Schubert.RS.PolynomialCompletionEvaluationWeights
import Schubert.RS.TorusCharacterTransport

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
open scoped BigOperators
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

variable {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
  (B : PolynomialRootStringBasis i.left i.right (compositionFlag (swapComposition u i)))

theorem PolynomialRootStringBasis.adjacentSourceTorus_eq :
    B.sourceTorus=compositionFlagTorus (swapComposition u i) := by
  apply MonoidHom.ext
  intro t
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  exact B.sourceTorus_val t p

/-- A bijective comparison preserving the source and lowering operator
identifies the completion character with the target flag character. -/
theorem PolynomialRootStringBasis.adjacent_character_of_bijective
    (f : B.completedModule i.left_ne_right →ₗ[ℂ] compositionFlag u)
    (hb : ∀ p : compositionFlag (swapComposition u i),
      (f (B.completionBoundary i.left_ne_right p)).val=p.val)
    (hf : ∀ x, (f ⁅sl2LoweringElement (polynomialSl2Triple i.left i.right i.left_ne_right),x⁆).val=
      matrixUnitDerivation i.right i.left (f x).val)
    (hbij : Function.Bijective f) :
    ∃ p : RS.Polynomial n,
      HasTorusCharacter (compositionFlagTorus (swapComposition u i)) p ∧
      HasTorusCharacter (compositionFlagTorus u) (isobaric i p) := by
  let p := ∑ j, partialStringCharacter i (B.residualExponent j) (B.length j)
  have hp : HasTorusCharacter B.sourceTorus p := B.hasPartialCharacter
  refine ⟨p,?_,?_⟩
  · rwa [B.adjacentSourceTorus_eq u i] at hp
  · let e : B.completedModule i.left_ne_right ≃ₗ[ℂ] compositionFlag u := LinearEquiv.ofBijective f hbij
    apply (B.completion_character_recursion p hp).of_equiv e
    intro t x
    apply Subtype.ext
    exact B.evaluation_torus i.left_ne_right ((compositionFlag u).subtype.comp f) hb hf t x

end
end Schubert.RS.Representation
