import Schubert.Demazure.ReflectedEndpointRelations
import Schubert.Demazure.Representation.PolynomialWeylEndpoint
import Schubert.Demazure.Representation.PolynomialCompletionEvaluation

/-!
# Joseph–Polo relations through the completed Weyl element

If `ξ` in a root-string completion satisfies the Joseph–Polo relations of `swapComposition u i`, and
`η` is a nonzero multiple of its image under the completed Weyl element satisfying the relation of
the simple root of `i` for `u`, then `η` satisfies all Joseph–Polo relations of `u`
(`completedWeyl_josephPolo_relations`).
-/

open Schubert

namespace Demazure.FlagModule
noncomputable section
open FinPermutation
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

variable {n : ℕ} {i : AdjacentPosition n} {S : Submodule ℂ (MatrixPolynomial n)}
  (B : PolynomialRootStringBasis i.left i.right S)
  (hE : ∀ p∈S, matrixUnitDerivation i.left i.right p∈S)
  (hR : ∀ r : RadicalRoot i, ∀ p∈S, matrixUnitDerivation r.val.val.1 r.val.val.2 p∈S)

theorem PolynomialRootStringBasis.completedWeyl_josephPolo_relations (u : Composition n)
    (ξ η : B.completedModule i.left_ne_right)
    (hξ : ∀ r : PositiveRoot n, B.completedUpperEnveloping hE hR
      (rootOperator r^josephPoloExponent (swapComposition u i) r) ξ=0)
    (s : ℂ) (hs : s≠0) (hη : B.completedWeyl i.left_ne_right ξ=s • η)
    (hsimple : B.completedUpperEnveloping hE hR
      (rootOperator (adjacentPositiveRoot i)^josephPoloExponent u (adjacentPositiveRoot i)) η=0) :
    ∀ r : PositiveRoot n, B.completedUpperEnveloping hE hR (rootOperator r^josephPoloExponent u r)
        η=0 := by
  classical
  let := B.completedUpperModule hE hR
  let := B.completedUpperTower hE hR
  let c : PositiveRoot n → ℂ := fun r =>
    if hr : r.val≠(i.left,i.right) then radicalWeylSign i (radicalReflectedRoot i ⟨r,hr⟩) else 1
  apply reflected_endpoint_josephPolo_relations u i ξ η
      (B.completedWeyl i.left_ne_right).toLinearMap
    hξ c ?_ s hs hη hsimple
  intro r hr x
  change B.completedUpperEnveloping hE hR (rootOperator r) (B.completedWeyl i.left_ne_right x)=
    c r • B.completedWeyl i.left_ne_right
      (B.completedUpperEnveloping hE hR (rootOperator (adjacentReflectedRoot i r hr)) x)
  have hc : c r=radicalWeylSign i (radicalReflectedRoot i ⟨r,hr⟩) := dite_eq_left hr
  exact (B.completedWeyl_root_transport hE hR ⟨r,hr⟩ x).trans
    (congrArg (fun z : ℂ => z • B.completedWeyl i.left_ne_right
      (B.completedUpperEnveloping hE hR (rootOperator (adjacentReflectedRoot i r hr)) x))
      hc.symm)

end
end Demazure.FlagModule
