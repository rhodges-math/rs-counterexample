import Schubert.RS.JosephPolo.LoweringCartan
import Schubert.RS.UpperRadicalGenerators

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 300000

theorem polynomialLie_matrix_entry {n : ℕ} (A : Square n) (a b : Fin n) :
    MvPolynomial.coeff (Finsupp.single (a,b) 1)
      (polynomialLie n A (MvPolynomial.X (b,b))) = A a b := by
  classical
  change MvPolynomial.coeff _ (rowDerivation A (MvPolynomial.X (b,b)))=_
  rw [rowDerivation_X, MvPolynomial.coeff_sum]
  simp [MvPolynomial.coeff_smul, MvPolynomial.coeff_X, Finsupp.single_left_inj]

theorem polynomialLie_injective (n : ℕ) : Function.Injective (polynomialLie n) := by
  intro A B h
  ext a b
  rw [← polynomialLie_matrix_entry A a b, ← polynomialLie_matrix_entry B a b, h]

theorem polynomialUpperLie_injective (n : ℕ) : Function.Injective (polynomialUpperLie n) := by
  intro A B h
  apply Subtype.ext
  exact polynomialLie_injective n h

theorem radicalEndSpan_le_upperRange {n : ℕ} (i : AdjacentPosition n) :
    radicalEndSpan i ≤ (polynomialUpperLie n).toLinearMap.range := by
  apply Submodule.span_le.mpr
  rintro _ ⟨r,rfl⟩
  exact ⟨rootVector r.val,rfl⟩

/-- Recover the unique strictly upper matrix behind a radical polynomial
operator. The inverse is justified by faithfulness on linear polynomials. -/
def radicalUpper {n : ℕ} (i : AdjacentPosition n) : radicalEndLie i →ₗ[ℂ] upperNilpotent n :=
  (LinearEquiv.ofInjective (polynomialUpperLie n).toLinearMap
    (polynomialUpperLie_injective n)).symm.toLinearMap.comp
      (Submodule.inclusion (radicalEndSpan_le_upperRange i))

theorem radicalUpper_polynomial {n : ℕ} (i : AdjacentPosition n) (r : radicalEndLie i) :
    polynomialUpperLie n (radicalUpper i r) = r.val := by
  let e := LinearEquiv.ofInjective (polynomialUpperLie n).toLinearMap
    (polynomialUpperLie_injective n)
  exact congrArg Subtype.val (e.apply_symm_apply (Submodule.inclusion (radicalEndSpan_le_upperRange i) r))

theorem radicalUpper_root {n : ℕ} (i : AdjacentPosition n) (r : RadicalRoot i) :
    radicalUpper i (radicalEndRoot i r)=rootVector r.val := by
  apply polynomialUpperLie_injective n
  rw [radicalUpper_polynomial]
  rfl

theorem radicalUpper_bracket {n : ℕ} (i : AdjacentPosition n) (r s : radicalEndLie i) :
    radicalUpper i ⁅r,s⁆ = ⁅radicalUpper i r,radicalUpper i s⁆ := by
  apply polynomialUpperLie_injective n
  rw [radicalUpper_polynomial, LieHom.map_lie, radicalUpper_polynomial, radicalUpper_polynomial]
  rfl

theorem radicalUpper_simple_zero {n : ℕ} (i : AdjacentPosition n) (r : radicalEndLie i) :
    upperSimpleCoefficient i (radicalUpper i r)=0 := by
  let f : radicalEndLie i →ₗ[ℂ] ℂ := (upperSimpleCoefficient i).comp (radicalUpper i)
  have hz : f=0 := by
    have hx (y : Module.End ℂ (MatrixPolynomial n)) (hy : y∈radicalEndSpan i) : f ⟨y,hy⟩=0 := by
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨s,rfl⟩ := hy
        change upperSimpleCoefficient i (radicalUpper i (radicalEndRoot i s))=0
        rw [radicalUpper_root, ← rootBasis_apply]
        exact upperSimpleCoefficient_root i s
      | zero => exact f.map_zero
      | add y z hy hz iy iz =>
        change f (⟨y,hy⟩+⟨z,hz⟩)=0
        rw [map_add, iy, iz, add_zero]
      | smul c y hy iy =>
        change f (c • ⟨y,hy⟩)=0
        rw [map_smul, iy, smul_zero]
    exact LinearMap.ext (fun x => hx x.val x.property)
  exact LinearMap.congr_fun hz r

end
end Schubert.RS.Representation
