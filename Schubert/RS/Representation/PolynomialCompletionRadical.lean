import Schubert.RS.PolynomialRootCompletion
import Schubert.RS.Representation.ParabolicRadicalAction
import Schubert.RS.Representation.RankOneRadicalModule

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ} {i : AdjacentPosition n} {S : Submodule ℂ (MatrixPolynomial n)}
  (B : PolynomialRootStringBasis i.left i.right S)
  (hE : ∀ p∈S, matrixUnitDerivation i.left i.right p∈S)
  (hR : ∀ r : RadicalRoot i, ∀ p∈S, matrixUnitDerivation r.val.val.1 r.val.val.2 p∈S)

theorem polynomialRadicalSource_e (z : radicalEndLie i ⊗[ℂ] S) :
    radicalPolynomialAction i S hR (tensorBorelOperator
      (sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right))
      (matrixUnitOnSubmodule i.left i.right S hE) z) =
      matrixUnitOnSubmodule i.left i.right S hE (radicalPolynomialAction i S hR z) :=
  radicalPolynomialAction_intertwines i S hR _ _ (fun _ => rfl) z

theorem PolynomialRootStringBasis.radicalSource_h (z : radicalEndLie i ⊗[ℂ] S) :
    radicalPolynomialAction i S hR (tensorBorelOperator
      (sl2CartanElement (polynomialSl2Triple i.left i.right i.left_ne_right))
      (B.cartan i.left_ne_right) z) = B.cartan i.left_ne_right (radicalPolynomialAction i S hR z) :=
  radicalPolynomialAction_intertwines i S hR _ _ (B.cartan_val i.left_ne_right) z

/-- The actual parabolic radical action on the constructed polynomial
rank-one completion. All compatibility inputs have been proved above. -/
def PolynomialRootStringBasis.completedRadicalAction :
    (radicalEndLie i ⊗[ℂ] B.completedModule i.left_ne_right) →ₗ⁅ℂ,
      (polynomialSl2Triple i.left i.right i.left_ne_right).toLieSubalgebra ℂ⁆
        B.completedModule i.left_ne_right :=
  (B.isCompletion i.left_ne_right hE).extendAction (radicalPolynomialAction i S hR)
    (polynomialRadicalSource_e hE hR) (B.radicalSource_h hR)

theorem PolynomialRootStringBasis.completedRadicalAction_boundary
    (r : radicalEndLie i) (p : S) :
    B.completedRadicalAction hE hR (r ⊗ₜ[ℂ] B.completionBoundary i.left_ne_right p) =
      B.completionBoundary i.left_ne_right (radicalPolynomialAction i S hR (r ⊗ₜ[ℂ] p)) :=
  (B.isCompletion i.left_ne_right hE).extendAction_boundary _ _ _ r p

theorem PolynomialRootStringBasis.completedRadicalAction_jacobi
    (r s : radicalEndLie i) (x : B.completedModule i.left_ne_right) :
    B.completedRadicalAction hE hR (⁅r,s⁆ ⊗ₜ[ℂ] x) =
      B.completedRadicalAction hE hR (r ⊗ₜ[ℂ] B.completedRadicalAction hE hR (s ⊗ₜ[ℂ] x)) -
      B.completedRadicalAction hE hR (s ⊗ₜ[ℂ] B.completedRadicalAction hE hR (r ⊗ₜ[ℂ] x)) :=
  (B.isCompletion i.left_ne_right hE).action_jacobi (radicalEndLie_levi_derivation i)
    (radicalPolynomialAction i S hR) (B.completedRadicalAction hE hR)
    (B.completedRadicalAction_boundary hE hR) (radicalPolynomialAction_jacobi i S hR) r s x

@[instance_reducible] def PolynomialRootStringBasis.completedRadicalLieRingModule :
    LieRingModule (radicalEndLie i) (B.completedModule i.left_ne_right) :=
  (B.isCompletion i.left_ne_right hE).radicalLieRingModule (radicalPolynomialAction i S hR)
    (polynomialRadicalSource_e hE hR) (B.radicalSource_h hR)
    (radicalEndLie_levi_derivation i) (radicalPolynomialAction_jacobi i S hR)

theorem PolynomialRootStringBasis.completedRadicalLieModule :
    @LieModule ℂ (radicalEndLie i) (B.completedModule i.left_ne_right) _ _ _ _ _
      (B.completedRadicalLieRingModule hE hR) :=
  (B.isCompletion i.left_ne_right hE).radicalLieModule (radicalPolynomialAction i S hR)
    (polynomialRadicalSource_e hE hR) (B.radicalSource_h hR)
    (radicalEndLie_levi_derivation i) (radicalPolynomialAction_jacobi i S hR)

theorem PolynomialRootStringBasis.completedRadical_isLieTower :
    letI := B.completedRadicalLieRingModule hE hR
    IsLieTower ((polynomialSl2Triple i.left i.right i.left_ne_right).toLieSubalgebra ℂ)
      (radicalEndLie i) (B.completedModule i.left_ne_right) :=
  (B.isCompletion i.left_ne_right hE).radical_isLieTower (radicalPolynomialAction i S hR)
    (polynomialRadicalSource_e hE hR) (B.radicalSource_h hR)
    (radicalEndLie_levi_derivation i) (radicalPolynomialAction_jacobi i S hR)

end
end Schubert.RS.Representation
