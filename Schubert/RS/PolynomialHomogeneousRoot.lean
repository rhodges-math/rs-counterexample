import Schubert.RS.FlagStringCharacter

namespace Schubert.RS.Representation
noncomputable section

theorem polynomialTorus_scalar_of_homogeneous {n D : ℕ} (p : MatrixPolynomial n)
    (hp : p.IsHomogeneous D) (c : ℂˣ) :
    polynomialTorus n (scalarTorus n c) p=(c:ℂ)^D • p := by
  ext d
  have he := basis_coord_eigenmap (MvPolynomial.basisMonomials (Fin n × Fin n) ℂ)
    (polynomialTorus n (scalarTorus n c)) (fun d => (c:ℂ)^d.sum (fun _ k => k))
    (fun d => polynomialTorus_scalar_monomial c d) d p
  change MvPolynomial.coeff d (polynomialTorus n (scalarTorus n c) p)=
    (c:ℂ)^d.sum (fun _ k => k) * MvPolynomial.coeff d p at he
  rw [he,MvPolynomial.coeff_smul,smul_eq_mul]
  by_cases hd : MvPolynomial.coeff d p=0
  · rw [hd,mul_zero,mul_zero]
  · have hdeg := hp hd
    have hs : d.sum (fun _ k => k)=D := by
      simpa [Finsupp.weight,Finsupp.linearCombination] using hdeg
    rw [hs]

/-- Every matrix-unit derivation preserves each actual homogeneous piece. -/
theorem matrixUnit_homogeneous {n D : ℕ} (a b : Fin n) (p : MatrixPolynomial n)
    (hp : p.IsHomogeneous D) : (matrixUnitDerivation a b p).IsHomogeneous D := by
  apply scalar_eigen_homogeneous
  rw [polynomialTorus_matrixUnit,polynomialTorus_scalar_of_homogeneous p hp,
    Derivation.map_smul]
  simp [rootScalar,scalarTorus]

theorem homogeneousPolynomial_le_degree (n D : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin n × Fin n) ℂ D≤
      MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ D := by
  intro p hp
  exact (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
    ((MvPolynomial.mem_homogeneousSubmodule D p).mp hp).totalDegree_le

instance homogeneousPolynomial_finite (n D : ℕ) :
    FiniteDimensional ℂ (MvPolynomial.homogeneousSubmodule (Fin n × Fin n) ℂ D) :=
  Module.Finite.of_injective (Submodule.inclusion (homogeneousPolynomial_le_degree n D))
    (Submodule.inclusion_injective _)

end
end Schubert.RS.Representation
