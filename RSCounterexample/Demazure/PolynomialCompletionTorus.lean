import RSCounterexample.Demazure.PolynomialRootCompletion
import RSCounterexample.Demazure.BasisWeightTorus
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Torus actions on root-string completions

A root-string basis of a torus-stable polynomial module has normalized torus weights, and the torus
acts on its source by `sourceTorus`. The completion gets the basis `completionBasis`, weights
`completionWeight` and a torus action `completionTorus`, compatible with the boundary inclusion
(`completionBoundary_torus`).
-/

open Schubert

namespace Demazure.FlagModule
noncomputable section
open TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 2000000

variable {n : ℕ} {a b : Fin n} {S : Submodule ℂ (MatrixPolynomial n)}
  (B : PolynomialRootStringBasis a b S) (hab : a≠b)

/-- The weight of a vector of the normalized basis,
`B.weight i + (length i - k) • positiveRoot a b`. -/
def PolynomialRootStringBasis.normalizedWeight (j : Σ i,Fin (B.length i+1)) : Weight n :=
  B.weight j.1+((B.length j.1:ℤ)-j.2.val) • positiveRoot a b

/-- The torus action on `S` that is diagonal in the normalized basis with weights
`normalizedWeight`. -/
def PolynomialRootStringBasis.sourceTorus : DiagonalTorus n →* Module.End ℂ S :=
  basisWeightTorus B.normalizedBasis B.normalizedWeight

theorem PolynomialRootStringBasis.normalizedBasis_weight (t : DiagonalTorus n)
    (j : Σ i,Fin (B.length i+1)) :
    polynomialTorus n t (B.normalizedBasis j : MatrixPolynomial n)=
      integerWeightScalar (B.normalizedWeight j) t •
          (B.normalizedBasis j : MatrixPolynomial n) := by
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

/-- The index of the basis of the completion: a string together with a position in each of the two
irreducible tensor factors. -/
abbrev PolynomialRootStringBasis.completionIndex :=
  Σ i : B.index, Fin (B.length i+1) × Fin (B.residual i+1)

/-- The basis of the completion formed by tensor products of the standard bases of the irreducible
factors. -/
def PolynomialRootStringBasis.completionBasis :
    Module.Basis B.completionIndex ℂ (B.completedModule hab) :=
  Pi.basis (fun i => (polynomialIrreducibleBasis a b hab (B.length i)).tensorProduct
    (polynomialIrreducibleBasis a b hab (B.residual i)))

/-- The torus weight of a vector of `completionBasis`. -/
def PolynomialRootStringBasis.completionWeight (j : B.completionIndex) : Weight n :=
  B.weight j.1+((B.length j.1:ℤ)-j.2.1.val-j.2.2.val) • positiveRoot a b

/-- The torus action on the completion that is diagonal in `completionBasis` with weights
`completionWeight`. -/
def PolynomialRootStringBasis.completionTorus : DiagonalTorus n →* Module.End ℂ
    (B.completedModule hab) :=
  basisWeightTorus (B.completionBasis hab) B.completionWeight

theorem PolynomialRootStringBasis.completionBoundary_basis (j : Σ i,Fin (B.length i+1)) :
    B.completionBoundary hab (B.normalizedBasis j)=B.completionBasis hab ⟨j.1,(j.2,0)⟩ := by
  classical
  rw [PolynomialRootStringBasis.completionBoundary,LinearMap.comp_apply,LinearEquiv.coe_coe,
    B.stringEquiv_basis hab j,piLinearMap_single,twistedPrimitiveBoundary_apply,
    PolynomialRootStringBasis.completionBasis,Pi.basis_apply,Module.Basis.tensorProduct_apply]
  rfl

theorem PolynomialRootStringBasis.completionBoundary_torus (t : DiagonalTorus n) (p : S) :
    B.completionBoundary hab (B.sourceTorus t p)=B.completionTorus hab t
        (B.completionBoundary hab p) := by
  exact basisWeightTorus_intertwines B.normalizedBasis B.normalizedWeight
    (B.completionBasis hab) B.completionWeight (B.completionBoundary hab)
    (fun j => ⟨j.1,(j.2,0)⟩) (B.completionBoundary_basis hab)
    (fun j => by simp [PolynomialRootStringBasis.normalizedWeight,
      PolynomialRootStringBasis.completionWeight]) t p

end
end Demazure.FlagModule
