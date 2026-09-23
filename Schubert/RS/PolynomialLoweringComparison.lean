import Schubert.RS.Representation.PrimitiveStringModule
import Schubert.RS.MatrixUnitStringWeights

namespace Schubert.RS.Representation
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
end Schubert.RS.Representation
