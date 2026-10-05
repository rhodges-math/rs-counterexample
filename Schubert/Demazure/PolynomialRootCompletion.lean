import Schubert.Demazure.PolynomialStringEquivOperators
import Schubert.Demazure.Representation.RankOnePiCompletion

/-!
# The rank-one completion of a polynomial module

For a root-string basis `B` of a polynomial module `S`, `completedModule` is the product over the
strings of tensor products of polynomial representations of the `sl₂` of the root. The boundary map
`completionBoundary` from `S` is injective and has the universal property of a rank-one completion
(`PolynomialRootStringBasis.isCompletion`).
-/

open Schubert

namespace Demazure.FlagModule
noncomputable section
open TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 2000000

variable {n : ℕ} {a b : Fin n} {S : Submodule ℂ (MatrixPolynomial n)}
  (B : PolynomialRootStringBasis a b S) (hab : a≠b)

/-- The finite rank-one completion is an actual product of tensor products
of polynomial root representations, one for each graded source string. -/
abbrev PolynomialRootStringBasis.completedModule :=
  ∀ i, polynomialIrreducible a b hab (B.length i) ⊗[ℂ]
    polynomialIrreducible a b hab (B.residual i)

/-- The boundary map from `S` into its root-string completion. -/
def PolynomialRootStringBasis.completionBoundary : S →ₗ[ℂ] B.completedModule hab :=
  (LinearMap.piMap (fun i => twistedPrimitiveBoundary (polynomialSl2Triple a b hab)
    (polynomialHighestVector_primitive a b hab (B.residual i))
    (polynomialIrreducible a b hab (B.length i)))).comp (B.stringEquiv hab).toLinearMap

/-- Existence, injection, and the universal mapping property for the actual
polynomial subspace with its actual raising and Cartan operators. Together
with `exists_polynomialRootStringBasis`, this applies to every finite
root- and torus-stable polynomial subspace. -/
theorem PolynomialRootStringBasis.isCompletion
    (hE : ∀ p∈S, matrixUnitDerivation a b p∈S) :
    IsRankOneCompletion (sl2RaisingElement (polynomialSl2Triple a b hab))
      (sl2CartanElement (polynomialSl2Triple a b hab))
      (matrixUnitOnSubmodule a b S hE) (B.cartan hab) (B.completionBoundary hab) := by
  let C := IsRankOneCompletion.pi (fun i : B.index =>
    twistedPrimitiveCompletion (polynomialSl2Triple a b hab)
      (polynomialHighestVector_primitive a b hab (B.residual i))
      (polynomialIrreducible a b hab (B.length i)))
  exact C.reparametrize (B.stringEquiv hab) (matrixUnitOnSubmodule a b S hE) (B.cartan hab)
    (B.stringEquiv_e hab hE) (B.stringEquiv_h hab)

theorem PolynomialRootStringBasis.completionBoundary_injective
    (hE : ∀ p∈S, matrixUnitDerivation a b p∈S) :
    Function.Injective (B.completionBoundary hab) :=
  (B.isCompletion hab hE).injective

end
end Demazure.FlagModule
