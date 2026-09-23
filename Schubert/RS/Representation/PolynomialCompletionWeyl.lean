import Schubert.RS.Representation.ParabolicRadicalWeyl
import Schubert.RS.Representation.PolynomialCompletionNilpotence
import Schubert.RS.Representation.PolynomialCompletionUpper

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

variable {n : ℕ} {a b : Fin n} {S : Submodule ℂ (MatrixPolynomial n)}
  (B : PolynomialRootStringBasis a b S) (hab : a≠b)

theorem PolynomialRootStringBasis.completedRaising_nilpotent :
    IsNilpotent (LieModule.toEnd ℂ _ (B.completedModule hab)
      (sl2RaisingElement (polynomialSl2Triple a b hab))) :=
  B.completedRoot_nilpotent hab _ a b hab rfl

theorem PolynomialRootStringBasis.completedLowering_nilpotent :
    IsNilpotent (LieModule.toEnd ℂ _ (B.completedModule hab)
      (sl2LoweringElement (polynomialSl2Triple a b hab))) :=
  B.completedRoot_nilpotent hab _ b a (Ne.symm hab) rfl

/-- The actual invertible algebraic Weyl operator on the constructed completion. -/
def PolynomialRootStringBasis.completedWeyl : B.completedModule hab ≃ₗ[ℂ] B.completedModule hab :=
  letI := complexRationalModule (B.completedModule hab)
  nilpotentWeylEquiv _ _ (B.completedRaising_nilpotent hab) (B.completedLowering_nilpotent hab)

theorem radicalReflectedRoot_involutive {n : ℕ} (i : AdjacentPosition n) (r : RadicalRoot i) :
    radicalReflectedRoot i (radicalReflectedRoot i r)=r := by
  apply Subtype.ext
  apply Subtype.ext
  simp [radicalReflectedRoot,adjacentTransposition]

theorem radicalWeylSign_mul_self {n : ℕ} (i : AdjacentPosition n) (r : RadicalRoot i) :
    radicalWeylSign i r * radicalWeylSign i r = 1 := by
  unfold radicalWeylSign
  split_ifs <;> norm_num

theorem smul_involution_symm {X : Type*} [AddCommGroup X] [Module ℂ X]
    (c : ℂ) (hc : c*c=1) {x y : X} (hxy : x=c • y) : y=c • x := by
  exact ((one_smul ℂ y).symm.trans (congrArg (· • y) hc.symm)).trans
    ((smul_smul c c y).symm.trans (congrArg (c • ·) hxy.symm))

variable {i : AdjacentPosition n} {S : Submodule ℂ (MatrixPolynomial n)}
  (B : PolynomialRootStringBasis i.left i.right S)
  (hE : ∀ p∈S, matrixUnitDerivation i.left i.right p∈S)
  (hR : ∀ r : RadicalRoot i, ∀ p∈S, matrixUnitDerivation r.val.val.1 r.val.val.2 p∈S)

theorem PolynomialRootStringBasis.completedWeyl_radical
    (r : radicalEndLie i) (x : B.completedModule i.left_ne_right) :
    B.completedWeyl i.left_ne_right (B.completedRadicalAction hE hR (r ⊗ₜ[ℂ] x)) =
      B.completedRadicalAction hE hR
        (radicalWeyl i r ⊗ₜ[ℂ] B.completedWeyl i.left_ne_right x) := by
  letI := complexRationalModule (radicalEndLie i)
  letI := complexRationalModule (B.completedModule i.left_ne_right)
  exact LieModuleHom.weyl_tensor_covariance (B.completedRadicalAction hE hR)
    (sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right))
    (sl2LoweringElement (polynomialSl2Triple i.left i.right i.left_ne_right))
    (radicalRaisingEnd_nilpotent i) (radicalLoweringEnd_nilpotent i)
    (B.completedRaising_nilpotent i.left_ne_right) (B.completedLowering_nilpotent i.left_ne_right) r x

theorem PolynomialRootStringBasis.completedWeyl_radicalRoot
    (r : RadicalRoot i) (x : B.completedModule i.left_ne_right) :
    B.completedRadicalAction hE hR
        (radicalEndRoot i r ⊗ₜ[ℂ] B.completedWeyl i.left_ne_right x) =
      radicalWeylSign i (radicalReflectedRoot i r) • B.completedWeyl i.left_ne_right
        (B.completedRadicalAction hE hR (radicalEndRoot i (radicalReflectedRoot i r) ⊗ₜ[ℂ] x)) := by
  let A := (B.completedRadicalAction hE hR).toLinearMap
  let w := B.completedWeyl i.left_ne_right
  let c := radicalWeylSign i (radicalReflectedRoot i r)
  have hr : radicalWeyl i (radicalEndRoot i (radicalReflectedRoot i r))=c • radicalEndRoot i r :=
    (radicalWeyl_root i (radicalReflectedRoot i r)).trans
      (congrArg (fun s => c • radicalEndRoot i s) (radicalReflectedRoot_involutive i r))
  have hc : w (A (radicalEndRoot i (radicalReflectedRoot i r) ⊗ₜ[ℂ] x))=
      c • A (radicalEndRoot i r ⊗ₜ[ℂ] w x) :=
    (B.completedWeyl_radical hE hR (radicalEndRoot i (radicalReflectedRoot i r)) x).trans
      ((congrArg (fun s => A (s ⊗ₜ[ℂ] w x)) hr).trans
        ((congrArg A (TensorProduct.smul_tmul' c (radicalEndRoot i r) (w x)).symm).trans
          (A.map_smul c (radicalEndRoot i r ⊗ₜ[ℂ] w x))))
  exact smul_involution_symm c (radicalWeylSign_mul_self i (radicalReflectedRoot i r)) hc

theorem upperSimpleCoefficient_radicalRoot {n : ℕ} (i : AdjacentPosition n) (r : RadicalRoot i) :
    upperSimpleCoefficient i (rootVector r.val)=0 := by
  rw [upperSimpleCoefficient_apply]
  change (Matrix.single r.val.val.1 r.val.val.2 (1:ℂ)) i.left i.right=0
  by_cases ha : r.val.val.1=i.left <;> by_cases hb : r.val.val.2=i.right
  · exact (r.property (Prod.ext ha hb)).elim
  all_goals simp [Matrix.single_apply,ha,hb,eq_comm]

theorem upperRadicalPart_radicalRoot {n : ℕ} (i : AdjacentPosition n) (r : RadicalRoot i) :
    upperRadicalPart i (rootVector r.val)=radicalEndRoot i r := by
  apply Subtype.ext
  rw [upperRadicalPart_val,upperSimpleCoefficient_radicalRoot,zero_smul,sub_zero]
  rfl

theorem PolynomialRootStringBasis.completedUpperEnveloping_radicalRoot
    (r : RadicalRoot i) (x : B.completedModule i.left_ne_right) :
    B.completedUpperEnveloping hE hR (rootOperator r.val) x =
      B.completedRadicalAction hE hR (radicalEndRoot i r ⊗ₜ[ℂ] x) := by
  let A := (B.completedRadicalAction hE hR).toLinearMap
  let ex := ⁅sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right),x⁆
  calc
    _ = B.completedUpperLie hE hR (rootVector r.val) x :=
      congrArg (fun D : Module.End ℂ (B.completedModule i.left_ne_right) => D x)
        (B.completedUpperEnveloping_ι hE hR (rootVector r.val))
    _ = upperSimpleCoefficient i (rootVector r.val) • ex +
        A (upperRadicalPart i (rootVector r.val) ⊗ₜ[ℂ] x) :=
      B.completedUpperLie_apply hE hR (rootVector r.val) x
    _ = 0 • ex + A (radicalEndRoot i r ⊗ₜ[ℂ] x) :=
      congrArg₂ (· + ·) (congrArg (· • ex) (upperSimpleCoefficient_radicalRoot i r))
        (congrArg (fun s => A (s ⊗ₜ[ℂ] x)) (upperRadicalPart_radicalRoot i r))
    _ = _ := (congrArg (· + A (radicalEndRoot i r ⊗ₜ[ℂ] x)) (zero_smul ℂ ex)).trans (zero_add _)

/-- Root transport in the orientation required by the JP relations. The
coefficient is the explicit sign of the reflected radical root. -/
theorem PolynomialRootStringBasis.completedWeyl_root_transport
    (r : RadicalRoot i) (x : B.completedModule i.left_ne_right) :
    B.completedUpperEnveloping hE hR (rootOperator r.val) (B.completedWeyl i.left_ne_right x) =
      radicalWeylSign i (radicalReflectedRoot i r) • B.completedWeyl i.left_ne_right
        (B.completedUpperEnveloping hE hR (rootOperator (radicalReflectedRoot i r).val) x) := by
  exact (B.completedUpperEnveloping_radicalRoot hE hR r (B.completedWeyl i.left_ne_right x)).trans
    ((B.completedWeyl_radicalRoot hE hR r x).trans
      (congrArg (fun y => radicalWeylSign i (radicalReflectedRoot i r) • B.completedWeyl i.left_ne_right y)
        (B.completedUpperEnveloping_radicalRoot hE hR (radicalReflectedRoot i r) x).symm))

end
end Schubert.RS.Representation
