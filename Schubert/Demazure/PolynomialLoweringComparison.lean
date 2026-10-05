import Schubert.Demazure.Representation.PrimitiveStringModule
import Schubert.Demazure.MatrixUnitStringWeights

/-!
# Comparing lowering strings with polynomials

A linear map `f` from a Lie module to polynomials with `f ⁅l, x⁆ = E_ab (f x)` sends the string
vectors `l^k x` to the iterated derivations `E_ab^k (f x)` (`polynomial_string_comparison`).
-/

open Schubert

namespace Demazure.FlagModule
noncomputable section

theorem polynomial_string_comparison {n : ℕ} {L X : Type*}
    [LieRing L] [LieAlgebra ℂ L] [AddCommGroup X] [Module ℂ X]
    [LieRingModule L X] [LieModule ℂ L X]
    (f : X →ₗ[ℂ] MatrixPolynomial n) (l : L) (a b : Fin n)
    (hf : ∀ x, f ⁅l,x⁆=matrixUnitDerivation a b (f x)) (x : X) (k : ℕ) :
    f (primitiveStringVector l x k)=derivationIter (matrixUnitDerivation a b) k (f x) := by
  induction k with
  | zero => simp
  | succ k ih => rw [primitiveStringVector_succ,derivationIter_succ,hf,ih]

end
end Demazure.FlagModule
