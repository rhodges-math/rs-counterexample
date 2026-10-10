import RSCounterexample.Demazure.Representation.Sl2WeylEndpoint
import RSCounterexample.Demazure.Representation.PolynomialCompletionWeyl

/-!
# The Weyl operator on highest vectors of completions

The Weyl operator `completedWeyl` anticommutes with the Cartan element (`completedWeyl_cartan`), and
sends a highest vector of weight `d` in the completion to a nonzero multiple of the end of its
lowering string (`completedWeyl_highest_endpoint`).
-/

open Schubert

namespace Demazure.FlagModule
noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

variable {n : ℕ} {a b : Fin n} {S : Submodule ℂ (MatrixPolynomial n)}
  (B : PolynomialRootStringBasis a b S) (hab : a≠b)

theorem PolynomialRootStringBasis.completedWeyl_cartan (x : B.completedModule hab) :
    ⁅sl2CartanElement (polynomialSl2Triple a b hab),B.completedWeyl hab x⁆ =
      -B.completedWeyl hab ⁅sl2CartanElement (polynomialSl2Triple a b hab),x⁆ := by
  let := complexRationalModule (B.completedModule hab)
  exact nilpotentWeyl_cartan (polynomialSl2Triple a b hab)
    (B.completedRaising_nilpotent hab) (B.completedLowering_nilpotent hab) x

/-- Highest-vector normalization of the actual completed-module Weyl
operator. The endpoint scalar is proved nonzero. -/
theorem PolynomialRootStringBasis.completedWeyl_highest_endpoint
    {m : B.completedModule hab} {d : ℕ}
    (P : (sl2SubalgebraTriple (polynomialSl2Triple a b hab)).HasPrimitiveVectorWith m (d:ℂ)) :
    ∃ c : ℂ, c≠0 ∧ B.completedWeyl hab m =
      c • primitiveStringVector (sl2LoweringElement (polynomialSl2Triple a b hab)) m d := by
  let := complexRationalModule (B.completedModule hab)
  exact nilpotentWeyl_highest_endpoint (polynomialSl2Triple a b hab)
    (B.completedRaising_nilpotent hab) (B.completedLowering_nilpotent hab) P

end
end Demazure.FlagModule
