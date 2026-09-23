import Schubert.RS.FlagStringCharacter
import Schubert.RS.Representation.CartanCommutators
import Mathlib.Algebra.Lie.Sl2

namespace Schubert.RS.Representation
noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

def polynomialRootCartan {n : ℕ} (a b : Fin n) : Module.End ℂ (MatrixPolynomial n) :=
  (matrixUnitDerivation a a).toLinearMap-(matrixUnitDerivation b b).toLinearMap

theorem polynomial_root_e_f {n : ℕ} (a b : Fin n) :
    ⁅(matrixUnitDerivation a b).toLinearMap,(matrixUnitDerivation b a).toLinearMap⁆=
      polynomialRootCartan a b := by
  apply LinearMap.ext
  intro p
  change matrixUnitDerivation a b (matrixUnitDerivation b a p)-
    matrixUnitDerivation b a (matrixUnitDerivation a b p)=
      matrixUnitDerivation a a p-matrixUnitDerivation b b p
  simpa using matrixUnitDerivation_commutator a b b a p

theorem polynomial_root_h_e {n : ℕ} (a b : Fin n) (hab : a≠b) :
    ⁅polynomialRootCartan a b,(matrixUnitDerivation a b).toLinearMap⁆=
      2 • (matrixUnitDerivation a b).toLinearMap := by
  apply LinearMap.ext
  intro p
  have h1 := matrixUnitDerivation_commutator a a a b p
  have h2 := matrixUnitDerivation_commutator b b a b p
  simp [hab,hab.symm] at h1 h2
  change (matrixUnitDerivation a a (matrixUnitDerivation a b p)-
    matrixUnitDerivation b b (matrixUnitDerivation a b p))-
    matrixUnitDerivation a b (matrixUnitDerivation a a p-matrixUnitDerivation b b p)=_
  rw [map_sub]
  change _=2 • matrixUnitDerivation a b p
  rw [two_nsmul]
  linear_combination h1-h2

theorem polynomial_root_h_f {n : ℕ} (a b : Fin n) (hab : a≠b) :
    ⁅polynomialRootCartan a b,(matrixUnitDerivation b a).toLinearMap⁆=
      -(2 • (matrixUnitDerivation b a).toLinearMap) := by
  have he := polynomial_root_h_e b a hab.symm
  have hh : polynomialRootCartan a b= -polynomialRootCartan b a := by
    unfold polynomialRootCartan
    abel
  rw [hh,neg_lie,he]

theorem polynomial_root_h_ne_zero {n : ℕ} (a b : Fin n) (hab : a≠b) :
    polynomialRootCartan a b≠0 := by
  intro h
  have hx := congrArg (fun f : Module.End ℂ (MatrixPolynomial n) => f (MvPolynomial.X (a,a))) h
  change matrixUnitDerivation a a (MvPolynomial.X (a,a))-
    matrixUnitDerivation b b (MvPolynomial.X (a,a))=0 at hx
  simp [matrixUnitDerivation_X,hab] at hx

/-- An actual sl2 triple of polynomial differential operators. -/
theorem polynomialSl2Triple {n : ℕ} (a b : Fin n) (hab : a≠b) :
    IsSl2Triple (polynomialRootCartan a b) (matrixUnitDerivation a b).toLinearMap
      (matrixUnitDerivation b a).toLinearMap where
  h_ne_zero := polynomial_root_h_ne_zero a b hab
  lie_e_f := polynomial_root_e_f a b
  lie_h_e_nsmul := polynomial_root_h_e a b hab
  lie_h_f_nsmul := polynomial_root_h_f a b hab

end
end Schubert.RS.Representation
