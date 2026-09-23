import Schubert.RS.MatrixUnitStringWeights
import Schubert.RS.NilpotentStringProjection

/-! A homogeneous functional on any nonzero polynomial weight vector,
constructed by extracting one of its nonzero monomial coefficients. -/

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators

def matrixMonomialTorusScalar {n : ℕ} (d : (Fin n × Fin n) →₀ ℕ)
    (t : DiagonalTorus n) : ℂ := ∏ rc ∈ d.support, (t rc.1 : ℂ) ^ d rc

theorem polynomialTorus_monomial {n : ℕ} (t : DiagonalTorus n)
    (d : (Fin n × Fin n) →₀ ℕ) :
    polynomialTorus n t (MvPolynomial.monomial d 1) =
      matrixMonomialTorusScalar d t • MvPolynomial.monomial d 1 := by
  classical
  change rowAction _ _ = _
  rw [← MvPolynomial.prod_X_pow_eq_monomial,map_prod]
  simp only [map_pow,show ∀ rc : Fin n × Fin n,
      rowAction (Matrix.diagonal (fun i => (t i : ℂ))) (MvPolynomial.X rc) =
      (t rc.1 : ℂ) • MvPolynomial.X rc from fun rc => polynomialTorus_X _ _ _,
    smul_pow,Finset.prod_smul,matrixMonomialTorusScalar]

theorem polynomialTorus_coeff {n : ℕ} (t : DiagonalTorus n)
    (d : (Fin n × Fin n) →₀ ℕ) (p : MatrixPolynomial n) :
    MvPolynomial.coeff d (polynomialTorus n t p) =
      matrixMonomialTorusScalar d t * MvPolynomial.coeff d p := by
  exact basis_coord_eigenmap (MvPolynomial.basisMonomials (Fin n × Fin n) ℂ)
    (polynomialTorus n t) (fun d => matrixMonomialTorusScalar d t)
    (polynomialTorus_monomial t) d p

def normalizedPolynomialCoefficient {n : ℕ} (d : (Fin n × Fin n) →₀ ℕ)
    (p : MatrixPolynomial n) : MatrixPolynomial n →ₗ[ℂ] ℂ :=
  (MvPolynomial.coeff d p)⁻¹ • MvPolynomial.lcoeff ℂ d

theorem normalizedPolynomialCoefficient_self {n : ℕ} (d : (Fin n × Fin n) →₀ ℕ)
    (p : MatrixPolynomial n) (hd : MvPolynomial.coeff d p≠0) :
    normalizedPolynomialCoefficient d p p=1 := by
  change (MvPolynomial.coeff d p)⁻¹ * MvPolynomial.coeff d p=1
  exact inv_mul_cancel₀ hd

theorem normalizedPolynomialCoefficient_equivariant {n : ℕ}
    (d : (Fin n × Fin n) →₀ ℕ) (p : MatrixPolynomial n)
    (hd : MvPolynomial.coeff d p≠0) (ν : DiagonalTorus n → ℂ)
    (hp : ∀ t, polynomialTorus n t p=ν t • p) (t : DiagonalTorus n)
    (x : MatrixPolynomial n) :
    normalizedPolynomialCoefficient d p (polynomialTorus n t x) =
      ν t * normalizedPolynomialCoefficient d p x := by
  have he : matrixMonomialTorusScalar d t=ν t := by
    apply mul_right_cancel₀ hd
    rw [← polynomialTorus_coeff,hp]
    simp
  change (MvPolynomial.coeff d p)⁻¹ * MvPolynomial.coeff d (polynomialTorus n t x) =
    ν t * ((MvPolynomial.coeff d p)⁻¹ * MvPolynomial.coeff d x)
  rw [polynomialTorus_coeff,he]
  ring

theorem exists_polynomial_weight_functional {n : ℕ} (p : MatrixPolynomial n)
    (hp0 : p≠0) (ν : DiagonalTorus n → ℂ)
    (hp : ∀ t, polynomialTorus n t p=ν t • p) :
    ∃ φ : MatrixPolynomial n →ₗ[ℂ] ℂ, φ p=1 ∧
      ∀ t x, φ (polynomialTorus n t x)=ν t * φ x := by
  obtain ⟨d,hd⟩ : ∃ d, MvPolynomial.coeff d p≠0 := by
    by_contra hn
    push Not at hn
    apply hp0
    ext d
    simpa using hn d
  exact ⟨normalizedPolynomialCoefficient d p,
    normalizedPolynomialCoefficient_self d p hd,
    normalizedPolynomialCoefficient_equivariant d p hd ν hp⟩

theorem homogeneous_functional_vanishes_of_weight_ne {n : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℂ V] (ρ : DiagonalTorus n → Module.End ℂ V)
    (φ : V →ₗ[ℂ] ℂ) (v w : Weight n) (hvw : v≠w)
    (hφ : ∀ t x, φ (ρ t x)=integerWeightScalar w t * φ x)
    (x : V) (hx : ∀ t, ρ t x=integerWeightScalar v t • x) : φ x=0 := by
  by_contra hzero
  apply hvw
  apply integerWeightScalar_injective
  funext t
  apply mul_right_cancel₀ hzero
  have he := hφ t x
  rw [hx t,map_smul,smul_eq_mul] at he
  exact he

/-- One concrete functional detects precisely the top of a nonzero matrix-unit
string and is homogeneous for the full torus. -/
theorem matrixUnit_string_top_functional {n : ℕ} (a b : Fin n) (hab : a≠b)
    (p : MatrixPolynomial n) (v : Weight n)
    (hp : ∀ t, polynomialTorus n t p=integerWeightScalar v t • p)
    (d : ℕ) (hd : derivationIter (matrixUnitDerivation a b) d p≠0) :
    ∃ φ : MatrixPolynomial n →ₗ[ℂ] ℂ,
      (∀ j≤d, φ (derivationIter (matrixUnitDerivation a b) j p)=if j=d then 1 else 0) ∧
      (∀ t x, φ (polynomialTorus n t x)=
        integerWeightScalar (v+d • positiveRoot a b) t * φ x) := by
  obtain ⟨φ,hφtop,hφ⟩ := exists_polynomial_weight_functional
    (derivationIter (matrixUnitDerivation a b) d p) hd
    (integerWeightScalar (v+d • positiveRoot a b))
    (matrixUnit_derivationIter_weight a b p v hp d)
  refine ⟨φ,?_,hφ⟩
  intro j hj
  by_cases hje : j=d
  · subst j
    simpa using hφtop
  · rw [if_neg hje]
    apply homogeneous_functional_vanishes_of_weight_ne (polynomialTorus n) φ
      (v+j • positiveRoot a b) (v+d • positiveRoot a b) ?_ hφ
      (derivationIter (matrixUnitDerivation a b) j p)
      (matrixUnit_derivationIter_weight a b p v hp j)
    intro he
    have ha := congrFun he a
    simp [positiveRoot,hab] at ha
    exact hje (by omega)

end
end Schubert.RS.Representation
