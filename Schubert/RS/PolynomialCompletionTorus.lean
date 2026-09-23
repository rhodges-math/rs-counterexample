import Schubert.RS.PolynomialRootCompletion
import Schubert.RS.BasisWeightTorus
import Mathlib.LinearAlgebra.TensorProduct.Basis

namespace Schubert.RS.Representation
noncomputable section
open TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 2000000

variable {n : ℕ} {a b : Fin n} {S : Submodule ℂ (MatrixPolynomial n)}
  (B : PolynomialRootStringBasis a b S) (hab : a≠b)

def PolynomialRootStringBasis.normalizedWeight (j : Σ i,Fin (B.length i+1)) : Weight n :=
  B.weight j.1+((B.length j.1:ℤ)-j.2.val) • positiveRoot a b

def PolynomialRootStringBasis.sourceTorus : DiagonalTorus n →* Module.End ℂ S :=
  basisWeightTorus B.normalizedBasis B.normalizedWeight

theorem PolynomialRootStringBasis.normalizedBasis_weight (t : DiagonalTorus n)
    (j : Σ i,Fin (B.length i+1)) :
    polynomialTorus n t (B.normalizedBasis j : MatrixPolynomial n)=
      integerWeightScalar (B.normalizedWeight j) t • (B.normalizedBasis j : MatrixPolynomial n) := by
  rw [B.normalizedBasis_val,map_smul,matrixUnit_derivationIter_weight a b _ _ (B.seed_weight j.1)]
  have hw : B.weight j.1+(B.length j.1-j.2.val) • positiveRoot a b=B.normalizedWeight j := by
    simp only [PolynomialRootStringBasis.normalizedWeight,← Nat.cast_smul_eq_nsmul ℤ,
      Nat.cast_sub (by omega : j.2.val≤B.length j.1)]
  rw [hw,smul_smul,smul_smul,mul_comm]

theorem PolynomialRootStringBasis.sourceTorus_val (t : DiagonalTorus n) (p : S) :
    (B.sourceTorus t p : MatrixPolynomial n)=polynomialTorus n t p.val := by
  have hh : S.subtype.comp (B.sourceTorus t)=(polynomialTorus n t).comp S.subtype := by
    apply B.normalizedBasis.ext
    intro j
    change (basisWeightTorus B.normalizedBasis B.normalizedWeight t (B.normalizedBasis j) :
      MatrixPolynomial n)=_
    rw [basisWeightTorus_basis]
    exact (B.normalizedBasis_weight t j).symm
  exact LinearMap.congr_fun hh p

abbrev PolynomialRootStringBasis.completionIndex :=
  Σ i : B.index, Fin (B.length i+1) × Fin (B.residual i+1)

def PolynomialRootStringBasis.completionBasis :
    Module.Basis B.completionIndex ℂ (B.completedModule hab) :=
  Pi.basis (fun i => (polynomialIrreducibleBasis a b hab (B.length i)).tensorProduct
    (polynomialIrreducibleBasis a b hab (B.residual i)))

def PolynomialRootStringBasis.completionWeight (j : B.completionIndex) : Weight n :=
  B.weight j.1+((B.length j.1:ℤ)-j.2.1.val-j.2.2.val) • positiveRoot a b

def PolynomialRootStringBasis.completionTorus : DiagonalTorus n →* Module.End ℂ (B.completedModule hab) :=
  basisWeightTorus (B.completionBasis hab) B.completionWeight

theorem PolynomialRootStringBasis.completionBoundary_basis (j : Σ i,Fin (B.length i+1)) :
    B.completionBoundary hab (B.normalizedBasis j)=B.completionBasis hab ⟨j.1,(j.2,0)⟩ := by
  classical
  rw [PolynomialRootStringBasis.completionBoundary,LinearMap.comp_apply,LinearEquiv.coe_coe,
    B.stringEquiv_basis hab j,piLinearMap_single,twistedPrimitiveBoundary_apply,
    PolynomialRootStringBasis.completionBasis,Pi.basis_apply,Module.Basis.tensorProduct_apply]
  rfl

theorem PolynomialRootStringBasis.completionBoundary_torus (t : DiagonalTorus n) (p : S) :
    B.completionBoundary hab (B.sourceTorus t p)=B.completionTorus hab t (B.completionBoundary hab p) := by
  exact basisWeightTorus_intertwines B.normalizedBasis B.normalizedWeight
    (B.completionBasis hab) B.completionWeight (B.completionBoundary hab)
    (fun j => ⟨j.1,(j.2,0)⟩) (B.completionBoundary_basis hab)
    (fun j => by simp [PolynomialRootStringBasis.normalizedWeight,
      PolynomialRootStringBasis.completionWeight]) t p

end
end Schubert.RS.Representation
