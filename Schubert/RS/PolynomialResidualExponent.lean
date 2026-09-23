import Schubert.RS.PolynomialCompletionWeights
import Schubert.RS.PartialStringCharacter

namespace Schubert.RS.Representation
noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ} {a b : Fin n} {S : Submodule ℂ (MatrixPolynomial n)}
  (B : PolynomialRootStringBasis a b S) (hab : a≠b)

def PolynomialRootStringBasis.residualWeight (i : B.index) : Weight n :=
  B.weight i-(B.length i:ℤ) • Pi.single b 1

include hab in
theorem PolynomialRootStringBasis.residualWeight_nonnegative (i : B.index) :
    ∀ c, 0≤B.residualWeight i c := by
  have hs := polynomial_weight_nonnegative _
    (derivationIter_ne_zero_of_le _ _ (Nat.zero_le _) (B.top_ne_zero i)) _ (B.seed_weight i)
  have ht := polynomial_weight_nonnegative _ (B.top_ne_zero i)
    (B.weight i+B.length i • positiveRoot a b)
    (matrixUnit_derivationIter_weight a b (B.seed i) (B.weight i)
      (B.seed_weight i) (B.length i))
  intro c
  by_cases hc : c=b
  · subst c
    simpa [PolynomialRootStringBasis.residualWeight,positiveRoot,hab,hab.symm] using ht b
  · simpa [PolynomialRootStringBasis.residualWeight,hc] using hs c

def PolynomialRootStringBasis.residualExponent (i : B.index) : Fin n →₀ ℕ :=
  nonnegativeWeightExponent (B.residualWeight i)

include hab in
theorem PolynomialRootStringBasis.residualExponent_weight (i : B.index) :
    exponentWeight (B.residualExponent i)=B.residualWeight i :=
  nonnegativeWeightExponent_weight _ (B.residualWeight_nonnegative hab i)

include hab in
theorem PolynomialRootStringBasis.residualExponent_left (i : B.index) :
    (B.residualExponent i a:ℤ)=B.weight i a := by
  have hh := congrFun (B.residualExponent_weight hab i) a
  change (B.residualExponent i a:ℤ)=_ at hh
  simpa [PolynomialRootStringBasis.residualWeight,hab] using hh

include hab in
theorem PolynomialRootStringBasis.residualExponent_right (i : B.index) :
    (B.residualExponent i b:ℤ)=B.weight i b-(B.length i:ℤ) := by
  have hh := congrFun (B.residualExponent_weight hab i) b
  change (B.residualExponent i b:ℤ)=_ at hh
  simpa [PolynomialRootStringBasis.residualWeight] using hh

include hab in
theorem PolynomialRootStringBasis.residualExponent_dominant (i : B.index) :
    B.residualExponent i b≤B.residualExponent i a := by
  have hleft := B.residualExponent_left hab i
  have hright := B.residualExponent_right hab i
  have hq := B.residual_cast_int hab i
  omega

include hab in
theorem PolynomialRootStringBasis.residualExponent_gap (i : B.index) :
    B.residualExponent i a-B.residualExponent i b=B.residual i := by
  have hleft := B.residualExponent_left hab i
  have hright := B.residualExponent_right hab i
  have hq := B.residual_cast_int hab i
  omega

end
end Schubert.RS.Representation
