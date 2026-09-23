import Schubert.RS.Representation.PolynomialCompletionEvaluation

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

variable {n : ℕ} {i : AdjacentPosition n} {S T : Submodule ℂ (MatrixPolynomial n)}
  (B : PolynomialRootStringBasis i.left i.right S)
  (hE : ∀ p∈S, matrixUnitDerivation i.left i.right p∈S)
  (hTE : ∀ p∈T, matrixUnitDerivation i.left i.right p∈T)
  (hTF : ∀ p∈T, matrixUnitDerivation i.right i.left p∈T)
  [Module.Finite ℂ T] (hST : S≤T)

/-- Evaluation with the native polynomial submodule as codomain. -/
def PolynomialRootStringBasis.completionEvaluationLinear :
    B.completedModule i.left_ne_right →ₗ[ℂ] T where
  toFun x := ⟨(B.completionEvaluation hE hTE hTF hST x).val,
    (B.completionEvaluation hE hTE hTF hST x).property⟩
  map_add' x y := Subtype.ext ((B.completionEvaluationPolynomial hE hTE hTF hST).map_add x y)
  map_smul' c x := Subtype.ext ((B.completionEvaluationPolynomial hE hTE hTF hST).map_smul c x)

theorem PolynomialRootStringBasis.completionEvaluationLinear_boundary (p : S) :
    (B.completionEvaluationLinear hE hTE hTF hST (B.completionBoundary i.left_ne_right p)).val=p.val :=
  congrArg Subtype.val (B.completionEvaluation_boundary hE hTE hTF hST p)

theorem PolynomialRootStringBasis.completionEvaluationLinear_lowering
    (x : B.completedModule i.left_ne_right) :
    (B.completionEvaluationLinear hE hTE hTF hST
      ⁅sl2LoweringElement (polynomialSl2Triple i.left i.right i.left_ne_right),x⁆).val=
      matrixUnitDerivation i.right i.left (B.completionEvaluationLinear hE hTE hTF hST x).val :=
  congrArg Subtype.val ((B.completionEvaluation hE hTE hTF hST).map_lie
    (sl2LoweringElement (polynomialSl2Triple i.left i.right i.left_ne_right)) x)

end
end Schubert.RS.Representation
