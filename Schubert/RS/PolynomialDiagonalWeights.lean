import Schubert.RS.PolynomialHomogeneousRoot
import Schubert.RS.Representation.CartanCommutators

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators

theorem diagonalDerivation_monomial {n : ℕ} (a : Fin n) (d : (Fin n × Fin n) →₀ ℕ) :
    matrixUnitDerivation a a (MvPolynomial.monomial d 1)=
      (matrixMonomialWeight d a : ℂ) • MvPolynomial.monomial d 1 := by
  classical
  have hx (rc : Fin n × Fin n) : matrixUnitDerivation a a (MvPolynomial.X rc)=
      (if rc.1=a then 1 else 0 : ℕ) • (MvPolynomial.X rc : MatrixPolynomial n) := by
    obtain ⟨r,c⟩ := rc
    by_cases hr : r=a
    · subst r; simp [matrixUnitDerivation_X]
    · simp [matrixUnitDerivation_X,hr]
  have h := derivation_eigen_prod (matrixUnitDerivation a a) d.support
    (fun rc => MvPolynomial.X rc^d rc) (fun rc => if rc.1=a then d rc else 0)
    (fun rc _ => by
      simpa only [ite_mul,one_mul,zero_mul] using
        derivation_eigen_pow (matrixUnitDerivation a a) (MvPolynomial.X rc)
          (if rc.1=a then 1 else 0) (hx rc) (d rc))
  have hs : (∑ rc∈d.support, if rc.1=a then d rc else 0)=∑ j,d (a,j) := by
    change d.sum (fun rc k => if rc.1=a then k else 0)=_
    rw [Finsupp.sum_fintype _ _ (fun _ => by simp),Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simp
  rw [hs,MvPolynomial.prod_X_pow_eq_monomial] at h
  change matrixUnitDerivation a a (MvPolynomial.monomial d 1)=
    ((∑ j,d (a,j) : ℕ):ℂ) • MvPolynomial.monomial d 1
  simpa only [Nat.cast_smul_eq_nsmul] using h

theorem polynomial_support_weight {n : ℕ} (p : MatrixPolynomial n) (v : Weight n)
    (hp : ∀ t, polynomialTorus n t p=integerWeightScalar v t • p)
    (d : (Fin n × Fin n) →₀ ℕ) (hd : MvPolynomial.coeff d p≠0) : matrixMonomialWeight d=v := by
  apply integerWeightScalar_injective
  funext t
  apply mul_right_cancel₀ hd
  rw [← polynomialTorus_coeff_weight,hp,MvPolynomial.coeff_smul,smul_eq_mul]

/-- Full torus weight determines the differentiated diagonal action, proved
by monomial coefficients rather than assuming a Lie/group compatibility axiom. -/
theorem diagonalDerivation_of_weight {n : ℕ} (a : Fin n) (p : MatrixPolynomial n)
    (v : Weight n) (hp : ∀ t, polynomialTorus n t p=integerWeightScalar v t • p) :
    matrixUnitDerivation a a p=(v a : ℂ) • p := by
  ext d
  have he := basis_coord_eigenmap (MvPolynomial.basisMonomials (Fin n × Fin n) ℂ)
    (matrixUnitDerivation a a).toLinearMap (fun d => (matrixMonomialWeight d a : ℂ))
    (diagonalDerivation_monomial a) d p
  change MvPolynomial.coeff d (matrixUnitDerivation a a p)=
    (matrixMonomialWeight d a : ℂ) * MvPolynomial.coeff d p at he
  rw [he,MvPolynomial.coeff_smul,smul_eq_mul]
  by_cases hd : MvPolynomial.coeff d p=0
  · rw [hd,mul_zero,mul_zero]
  · rw [polynomial_support_weight p v hp d hd]

end
end Schubert.RS.Representation
