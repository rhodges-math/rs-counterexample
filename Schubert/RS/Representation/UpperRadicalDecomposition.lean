import Schubert.RS.Representation.ParabolicRadicalLie
import Schubert.RS.Representation.PrimitiveStringExtension

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
open scoped BigOperators
attribute [local instance 100] LieRing.ofAssociativeRing

def adjacentPositiveRoot {n : ℕ} (i : AdjacentPosition n) : PositiveRoot n :=
  ⟨(i.left,i.right),i.left_lt_right⟩

theorem rootBasis_repr_entry {n : ℕ} (A : upperNilpotent n) (r : PositiveRoot n) :
    (rootBasis n).repr A r = A.val r.val.1 r.val.2 := by
  simp [rootBasis,rootCoordinates]
  rfl

def upperSimpleCoefficient {n : ℕ} (i : AdjacentPosition n) : upperNilpotent n →ₗ[ℂ] ℂ :=
  (rootBasis n).coord (adjacentPositiveRoot i)

theorem upperSimpleCoefficient_apply {n : ℕ} (i : AdjacentPosition n) (A : upperNilpotent n) :
    upperSimpleCoefficient i A = A.val i.left i.right :=
  rootBasis_repr_entry A (adjacentPositiveRoot i)

def upperRadicalRemainder {n : ℕ} (i : AdjacentPosition n) :
    upperNilpotent n →ₗ[ℂ] Module.End ℂ (MatrixPolynomial n) :=
  (polynomialUpperLie n).toLinearMap -
    (upperSimpleCoefficient i).smulRight (matrixUnitDerivation i.left i.right).toLinearMap

theorem upperRadicalRemainder_mem {n : ℕ} (i : AdjacentPosition n) (A : upperNilpotent n) :
    upperRadicalRemainder i A ∈ radicalEndSpan i := by
  classical
  have hr : ∀ r : PositiveRoot n, upperRadicalRemainder i (rootBasis n r)∈radicalEndSpan i := by
    intro r
    by_cases he : r=adjacentPositiveRoot i
    · subst r
      have hz : upperSimpleCoefficient i (rootBasis n (adjacentPositiveRoot i))=1 := by
        simp [upperSimpleCoefficient,Module.Basis.coord_apply]
      change polynomialUpperLie n (rootBasis n (adjacentPositiveRoot i)) -
        upperSimpleCoefficient i (rootBasis n (adjacentPositiveRoot i)) •
          (matrixUnitDerivation i.left i.right).toLinearMap∈_
      rw [hz,one_smul,rootBasis_apply]
      change (matrixUnitDerivation i.left i.right).toLinearMap -
        (matrixUnitDerivation i.left i.right).toLinearMap ∈ _
      rw [sub_self]
      exact (radicalEndSpan i).zero_mem
    · have hre : r.val≠(i.left,i.right) := fun hh => he (Subtype.ext hh)
      have hz : upperSimpleCoefficient i (rootBasis n r)=0 := by
        simp [upperSimpleCoefficient,Module.Basis.coord_apply,he,Ne.symm he]
      change polynomialUpperLie n (rootBasis n r) -
        upperSimpleCoefficient i (rootBasis n r) • (matrixUnitDerivation i.left i.right).toLinearMap∈_
      rw [hz,zero_smul,sub_zero,rootBasis_apply]
      exact radicalEndSpan_root_mem i ⟨r,hre⟩
  rw [← (rootBasis n).sum_repr A,map_sum]
  apply (radicalEndSpan i).sum_mem
  intro r _
  rw [map_smul]
  exact (radicalEndSpan i).smul_mem _ (hr r)

def upperRadicalPart {n : ℕ} (i : AdjacentPosition n) : upperNilpotent n →ₗ[ℂ] radicalEndLie i :=
  (upperRadicalRemainder i).codRestrict (radicalEndSpan i) (upperRadicalRemainder_mem i)

theorem upperRadicalPart_val {n : ℕ} (i : AdjacentPosition n) (A : upperNilpotent n) :
    (upperRadicalPart i A).val = polynomialUpperLie n A -
      upperSimpleCoefficient i A • (matrixUnitDerivation i.left i.right).toLinearMap := rfl

theorem polynomialUpperLie_decomposition {n : ℕ} (i : AdjacentPosition n) (A : upperNilpotent n) :
    polynomialUpperLie n A = upperSimpleCoefficient i A •
      (matrixUnitDerivation i.left i.right).toLinearMap + (upperRadicalPart i A).val := by
  rw [upperRadicalPart_val]
  abel

private theorem upper_adjacent_mul_zero {n : ℕ} (i : AdjacentPosition n) (A B : upperNilpotent n) :
    (A.val*B.val) i.left i.right=0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : i.left<k
  · have hkr : ¬ (k < i.right) := by
      have hi := i.right_val
      change i.left.val < k.val at hk
      change ¬ (k.val < i.right.val)
      omega
    rw [B.property k i.right hkr,mul_zero]
  · rw [A.property i.left k hk,zero_mul]

theorem upperSimpleCoefficient_bracket {n : ℕ} (i : AdjacentPosition n) (A B : upperNilpotent n) :
    upperSimpleCoefficient i ⁅A,B⁆ = 0 := by
  rw [upperSimpleCoefficient_apply]
  change (A.val*B.val) i.left i.right - (B.val*A.val) i.left i.right=0
  rw [upper_adjacent_mul_zero,upper_adjacent_mul_zero,sub_zero]

theorem upperRadicalPart_bracket {n : ℕ} (i : AdjacentPosition n) (A B : upperNilpotent n) :
    upperRadicalPart i ⁅A,B⁆ =
      upperSimpleCoefficient i A •
        ⁅sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right),upperRadicalPart i B⁆ -
      upperSimpleCoefficient i B •
        ⁅sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right),upperRadicalPart i A⁆ +
      ⁅upperRadicalPart i A,upperRadicalPart i B⁆ := by
  apply Subtype.ext
  rw [upperRadicalPart_val,upperSimpleCoefficient_bracket,zero_smul,sub_zero,
    LieHom.map_lie,polynomialUpperLie_decomposition i A,polynomialUpperLie_decomposition i B]
  change ⁅upperSimpleCoefficient i A • (matrixUnitDerivation i.left i.right).toLinearMap +
      (upperRadicalPart i A).val,
      upperSimpleCoefficient i B • (matrixUnitDerivation i.left i.right).toLinearMap +
      (upperRadicalPart i B).val⁆ = _
  change _ = upperSimpleCoefficient i A •
      ⁅(matrixUnitDerivation i.left i.right).toLinearMap,(upperRadicalPart i B).val⁆ -
    upperSimpleCoefficient i B •
      ⁅(matrixUnitDerivation i.left i.right).toLinearMap,(upperRadicalPart i A).val⁆ +
    ⁅(upperRadicalPart i A).val,(upperRadicalPart i B).val⁆
  simp only [Ring.lie_def,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,smul_sub]
  module

end
end Schubert.RS.Representation
