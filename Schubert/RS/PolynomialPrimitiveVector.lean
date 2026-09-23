import Schubert.RS.PolynomialRootModule
import Schubert.RS.Representation.PrimitiveStringExtension

namespace Schubert.RS.Representation
noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

/-- An actual highest vector of every nonnegative integral weight, in the
finite homogeneous piece of the polynomial representation. -/
def polynomialHighestVector {n : ℕ} (a b : Fin n) (hab : a≠b) (d : ℕ) :
    homogeneousPolynomialRootModule a b hab d :=
  ⟨MvPolynomial.X (a,a)^d, by
    change (MvPolynomial.X (a,a)^d).IsHomogeneous d
    simpa using (MvPolynomial.isHomogeneous_X ℂ (a,a)).pow d⟩

theorem polynomialHighestVector_ne_zero {n : ℕ} (a b : Fin n) (hab : a≠b) (d : ℕ) :
    polynomialHighestVector a b hab d≠0 := by
  intro h
  have hh := congrArg Subtype.val h
  exact pow_ne_zero d (MvPolynomial.X_ne_zero (a,a)) hh

theorem polynomialHighestVector_e {n : ℕ} (a b : Fin n) (hab : a≠b) (d : ℕ) :
    ⁅sl2RaisingElement (polynomialSl2Triple a b hab),
      polynomialHighestVector a b hab d⁆ = 0 := by
  apply Subtype.ext
  change matrixUnitDerivation a b (MvPolynomial.X (a,a)^d)=0
  simp [Derivation.leibniz_pow,matrixUnitDerivation_X,hab]

theorem polynomialHighestVector_h {n : ℕ} (a b : Fin n) (hab : a≠b) (d : ℕ) :
    ⁅sl2CartanElement (polynomialSl2Triple a b hab),
      polynomialHighestVector a b hab d⁆ = (d:ℂ) • polynomialHighestVector a b hab d := by
  apply Subtype.ext
  change matrixUnitDerivation a a (MvPolynomial.X (a,a)^d)-
    matrixUnitDerivation b b (MvPolynomial.X (a,a)^d)=
    (d:ℂ) • (MvPolynomial.X (a,a)^d)
  have ha : matrixUnitDerivation a a (MvPolynomial.X (a,a))=
      1 • MvPolynomial.X (a,a) := by simp [matrixUnitDerivation_X]
  have hb : matrixUnitDerivation b b (MvPolynomial.X (a,a))=
      0 • MvPolynomial.X (a,a) := by simp [matrixUnitDerivation_X,hab]
  rw [derivation_eigen_pow _ _ 1 ha,derivation_eigen_pow _ _ 0 hb]
  simp only [one_mul,zero_mul,zero_nsmul,sub_zero,Nat.cast_smul_eq_nsmul]

theorem polynomialHighestVector_primitive {n : ℕ} (a b : Fin n) (hab : a≠b) (d : ℕ) :
    (sl2SubalgebraTriple (polynomialSl2Triple a b hab)).HasPrimitiveVectorWith
      (polynomialHighestVector a b hab d) (d:ℂ) where
  ne_zero := polynomialHighestVector_ne_zero a b hab d
  lie_h := polynomialHighestVector_h a b hab d
  lie_e := polynomialHighestVector_e a b hab d

end
end Schubert.RS.Representation
