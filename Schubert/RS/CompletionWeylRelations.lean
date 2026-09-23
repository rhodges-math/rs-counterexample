import Schubert.RS.ReflectedEndpointRelations
import Schubert.RS.Representation.PolynomialWeylEndpoint
import Schubert.RS.Representation.PolynomialCompletionEvaluation

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

variable {n : ℕ} {i : AdjacentPosition n} {S : Submodule ℂ (MatrixPolynomial n)}
  (B : PolynomialRootStringBasis i.left i.right S)
  (hE : ∀ p∈S, matrixUnitDerivation i.left i.right p∈S)
  (hR : ∀ r : RadicalRoot i, ∀ p∈S, matrixUnitDerivation r.val.val.1 r.val.val.2 p∈S)

theorem PolynomialRootStringBasis.completedWeyl_jp_relations (u : Composition n)
    (ξ η : B.completedModule i.left_ne_right)
    (hξ : ∀ r : PositiveRoot n, B.completedUpperEnveloping hE hR
      (rootOperator r^jpExponent (swapComposition u i) r) ξ=0)
    (s : ℂ) (hs : s≠0) (hη : B.completedWeyl i.left_ne_right ξ=s • η)
    (hsimple : B.completedUpperEnveloping hE hR
      (rootOperator (adjacentPositiveRoot i)^jpExponent u (adjacentPositiveRoot i)) η=0) :
    ∀ r : PositiveRoot n, B.completedUpperEnveloping hE hR (rootOperator r^jpExponent u r) η=0 := by
  classical
  letI := B.completedUpperModule hE hR
  letI := B.completedUpperTower hE hR
  let c : PositiveRoot n → ℂ := fun r =>
    if hr : r.val≠(i.left,i.right) then radicalWeylSign i (radicalReflectedRoot i ⟨r,hr⟩) else 1
  apply reflected_endpoint_jp_relations u i ξ η (B.completedWeyl i.left_ne_right).toLinearMap
    hξ c ?_ s hs hη hsimple
  intro r hr x
  change B.completedUpperEnveloping hE hR (rootOperator r) (B.completedWeyl i.left_ne_right x)=
    c r • B.completedWeyl i.left_ne_right
      (B.completedUpperEnveloping hE hR (rootOperator (adjacentReflectedRoot i r hr)) x)
  have hc : c r=radicalWeylSign i (radicalReflectedRoot i ⟨r,hr⟩) := dif_pos hr
  exact (B.completedWeyl_root_transport hE hR ⟨r,hr⟩ x).trans
    (congrArg (fun z : ℂ => z • B.completedWeyl i.left_ne_right
      (B.completedUpperEnveloping hE hR (rootOperator (adjacentReflectedRoot i r hr)) x))
      hc.symm)

end
end Schubert.RS.Representation
