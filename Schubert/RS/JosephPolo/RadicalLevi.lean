import Schubert.RS.JosephPolo.RadicalMatrices
import Schubert.RS.JosephPolo.CartanCovariance

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 400000

theorem radicalUpper_raising {n : ℕ} (i : AdjacentPosition n) (r : radicalEndLie i) :
    radicalUpper i ⁅sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right),r⁆ =
      ⁅rootVector (adjacentPositiveRoot i),radicalUpper i r⁆ := by
  apply polynomialUpperLie_injective n
  rw [radicalUpper_polynomial, LieHom.map_lie, radicalUpper_polynomial]
  rfl

theorem radicalUpper_cartan {n : ℕ} (i : AdjacentPosition n) (r : radicalEndLie i) :
    radicalUpper i ⁅sl2CartanElement (polynomialSl2Triple i.left i.right i.left_ne_right),r⁆ =
      cartanUpper (adjacentCartanDiagonal i) (radicalUpper i r) := by
  apply polynomialUpperLie_injective n
  rw [radicalUpper_polynomial]
  have hm : (cartanUpper (adjacentCartanDiagonal i) (radicalUpper i r)).val =
      ⁅adjacentCartanMatrix i,(radicalUpper i r).val⁆ := by
    change cartanMatrix (adjacentCartanDiagonal i) (radicalUpper i r).val=_
    rw [cartanMatrix_eq_commutator, adjacentCartanMatrix_eq_diagonal]
    rfl
  change ⁅polynomialRootCartan i.left i.right,r.val⁆ =
    polynomialLie n (cartanUpper (adjacentCartanDiagonal i) (radicalUpper i r)).val
  rw [hm, LieHom.map_lie, polynomialLie_adjacentCartan]
  change _=⁅polynomialRootCartan i.left i.right,polynomialUpperLie n (radicalUpper i r)⁆
  rw [radicalUpper_polynomial]

theorem radicalUpper_lowering {n : ℕ} (i : AdjacentPosition n) (r : radicalEndLie i) :
    radicalUpper i ⁅sl2LoweringElement (polynomialSl2Triple i.left i.right i.left_ne_right),r⁆ =
      loweringUpper i (radicalUpper i r) := by
  apply polynomialUpperLie_injective n
  rw [radicalUpper_polynomial]
  have hm : (loweringUpper i (radicalUpper i r)).val =
      ⁅Matrix.single i.right i.left (1 : ℂ),(radicalUpper i r).val⁆ := by
    change Matrix.single i.right i.left 1*(radicalUpper i r).val-
      (radicalUpper i r).val*Matrix.single i.right i.left 1+
        upperSimpleCoefficient i (radicalUpper i r) • adjacentCartanMatrix i=_
    rw [radicalUpper_simple_zero, zero_smul, add_zero]
    rfl
  change ⁅(matrixUnitDerivation i.right i.left).toLinearMap,r.val⁆ =
    polynomialLie n (loweringUpper i (radicalUpper i r)).val
  rw [hm, LieHom.map_lie]
  change _=⁅(matrixUnitDerivation i.right i.left).toLinearMap,
    polynomialUpperLie n (radicalUpper i r)⁆
  rw [radicalUpper_polynomial]

end
end Schubert.RS.Representation
