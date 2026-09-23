import Schubert.RS.BoxCoordinates
import Schubert.RS.AtomExpansionCertificate
import Schubert.RS.Representation.CompositionFlag
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Integral atom expansion existence from proved duality. On every finite
exponent box the atom coordinate matrix has an integral left inverse, hence
an integral right inverse. This is a basis proof, not an added basis input. -/

namespace Schubert.RS
noncomputable section
open Representation
variable {n w : ℕ}

def boxAtomMatrix (n w : ℕ) : Matrix (BoxIndex n w) (BoxIndex n w) ℤ :=
  fun u v => boxCoordinates (atom (boxComposition v)) u

def boxDualMatrix (n w : ℕ) : Matrix (BoxIndex n w) (BoxIndex n w) ℤ :=
  fun u v => rectangleCoefficient w (boxComposition u) (compositionMonomial (boxComposition v))

def boxAtomSum (v : BoxIndex n w → ℤ) : Polynomial n :=
  ∑ u,v u • atom (boxComposition u)

theorem boxAtomSum_mem (v : BoxIndex n w → ℤ) : boxAtomSum v∈exponentBox n w := by
  apply (exponentBox n w).sum_mem
  intro u _
  exact (exponentBox n w).smul_mem _ (atom_mem_exponentBox w _ (boxComposition_bound u))

theorem boxAtomSum_coordinates (v : BoxIndex n w → ℤ) :
    boxCoordinates (boxAtomSum v)=(boxAtomMatrix n w).mulVec v := by
  funext u
  simp only [boxCoordinates,boxAtomSum,MvPolynomial.coeff_sum,MvPolynomial.coeff_smul,
    Matrix.mulVec,dotProduct,boxAtomMatrix,smul_eq_mul]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem boxDualMatrix_mulVec (f : Polynomial n) (hf : f∈exponentBox n w) :
    (boxDualMatrix n w).mulVec (boxCoordinates f)=
      (fun u => rectangleCoefficient w (boxComposition u) f) := by
  funext u
  have he:=congrArg (rectangleCoefficientLinear w (boxComposition u)) (boxDecode_coordinates f hf)
  simp only [boxDecode,map_sum,map_smul] at he
  change (∑ v,boxCoordinates f v*boxDualMatrix n w u v)=rectangleCoefficient w (boxComposition u) f at he
  change (∑ v,boxDualMatrix n w u v*boxCoordinates f v)=_
  rw [← he]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem boxMatrices_left_inverse
    (hdual : ∀ u v : BoxIndex n w,
      rectangleCoefficient w (boxComposition u) (atom (boxComposition v))=if v=u then 1 else 0) :
    boxDualMatrix n w*boxAtomMatrix n w=1 := by
  ext u v
  have he:=congrFun (boxDualMatrix_mulVec (atom (boxComposition v))
    (atom_mem_exponentBox w _ (boxComposition_bound v))) u
  rw [hdual] at he
  simpa only [Matrix.mul_apply,Matrix.mulVec,dotProduct,boxAtomMatrix,Matrix.one_apply,eq_comm (a:=v) (b:=u)] using he

theorem boxAtomSum_reconstruct
    (hdual : ∀ u v : BoxIndex n w,
      rectangleCoefficient w (boxComposition u) (atom (boxComposition v))=if v=u then 1 else 0)
    (f : Polynomial n) (hf : f∈exponentBox n w) :
    boxAtomSum (fun u : BoxIndex n w => rectangleCoefficient w (boxComposition u) f)=f := by
  have hr : boxAtomMatrix n w*boxDualMatrix n w=1 :=
    mul_eq_one_comm.mp (boxMatrices_left_inverse hdual)
  apply boxCoordinates_injective_on (boxAtomSum_mem _) hf
  rw [boxAtomSum_coordinates,← boxDualMatrix_mulVec f hf,Matrix.mulVec_mulVec,hr,Matrix.one_mulVec]

theorem boxed_atom_expansion
    (hJP : ∀ u : Composition n,CompositionFlagJosephPolo u)
    (hDCF : ∀ u : Composition n,CompositionFlagDemazureCharacter u) (hpbw : HasOrderedPBWBasis n)
    (w : ℕ) (f : Polynomial n) (hf : f∈exponentBox n w) :
    f=∑ u : BoxIndex n w,rectangleCoefficient w (boxComposition u) f • atom (boxComposition u) := by
  symm
  apply boxAtomSum_reconstruct
  · intro u v
    rw [rectangleCoefficient_atom compositionFlagTorus compositionFlagGenerator
      hJP hDCF hpbw w (boxComposition u) (boxComposition v) (boxComposition_bound u)]
    simp only [boxComposition_injective.eq_iff]
  · exact hf

end
end Schubert.RS

