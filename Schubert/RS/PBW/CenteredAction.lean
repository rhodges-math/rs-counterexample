import Schubert.RS.PBW.Jets
import Schubert.RS.Representation.MinorStrings
import Schubert.RS.Representation.KillingWordFiltration

/-! Center the genuine polynomial representation at the identity matrix. -/
namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators
open MvPolynomial
open Schubert.RS.PBW

private theorem derivation_sum_apply {n : ℕ} {α : Type*} (s : Finset α)
    (f : α → Derivation ℂ (MatrixPolynomial n) (MatrixPolynomial n))
    (p : MatrixPolynomial n) : (∑ i ∈ s, f i) p = ∑ i ∈ s, f i p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert hi, Derivation.add_apply, ih]

def rootCoordinate {n : ℕ} (r : PositiveRoot n) : Fin n × Fin n := (r.val.2, r.val.1)

theorem rootCoordinate_injective (n : ℕ) : Function.Injective (rootCoordinate (n := n)) := by
  intro r s h
  apply Subtype.ext
  exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)

def centeredRootDerivative {n : ℕ} (r : PositiveRoot n) :
    Derivation ℂ (MatrixPolynomial n) (MatrixPolynomial n) :=
  matrixUnitDerivation r.val.1 r.val.2 + pderiv (rootCoordinate r)

theorem matrixUnitDerivation_eq_sum {n : ℕ} (a b : Fin n) :
    matrixUnitDerivation a b =
      ∑ j : Fin n, (X (a,j) : MatrixPolynomial n) • pderiv (b,j) := by
  apply MvPolynomial.derivation_ext
  rintro ⟨i,k⟩
  simp only [matrixUnitDerivation_X, derivation_sum_apply, Derivation.smul_apply,
    pderiv_X, Pi.single_apply, smul_eq_mul]
  by_cases h : i = b
  · subst i
    simp [Prod.ext_iff, eq_comm]
  · simp [Prod.ext_iff, h, Ne.symm h]

theorem matrixUnitDerivation_mem_jet {n : ℕ} (a b : Fin n) (d : ℕ)
    (p : MatrixPolynomial n) (hp : p ∈ jet d) : matrixUnitDerivation a b p ∈ jet d := by
  rw [matrixUnitDerivation_eq_sum, derivation_sum_apply]
  apply Submodule.sum_mem
  intro j hj
  exact X_pderiv_mem_jet (a,j) (b,j) hp

theorem centeredRootDerivative_lowers {n : ℕ} (r : PositiveRoot n) (d : ℕ)
    (p : MatrixPolynomial n) (hp : p ∈ jet (d+1)) : centeredRootDerivative r p ∈ jet d := by
  exact (jet d).add_mem
    (jet_antitone (Nat.le_succ d) (matrixUnitDerivation_mem_jet _ _ _ _ hp))
    (pderiv_mem_jet _ hp)

theorem centeredRootDerivative_error {n : ℕ} (r : PositiveRoot n) (d : ℕ)
    (p : MatrixPolynomial n) (hp : p ∈ jet d) :
    centeredRootDerivative r p - pderiv (rootCoordinate r) p ∈ jet d := by
  simpa [centeredRootDerivative] using matrixUnitDerivation_mem_jet r.val.1 r.val.2 d p hp

def centerPolynomial (n : ℕ) : MatrixPolynomial n →ₐ[ℂ] MatrixPolynomial n :=
  aeval (fun ij => X ij - C (if ij.1 = ij.2 then 1 else 0 : ℂ))

def evaluateIdentity (n : ℕ) : MatrixPolynomial n →ₐ[ℂ] ℂ :=
  aeval (fun ij => if ij.1 = ij.2 then 1 else 0)

theorem evaluateIdentity_center {n : ℕ} (p : MatrixPolynomial n) :
    evaluateIdentity n (centerPolynomial n p) = coeff 0 p := by
  have h : (evaluateIdentity n).comp (centerPolynomial n) =
      aeval (fun _ : Fin n × Fin n => (0 : ℂ)) := by
    apply MvPolynomial.algHom_ext
    intro ij
    simp [centerPolynomial, evaluateIdentity]
  have hp := AlgHom.congr_fun h p
  simpa [aeval_zero', constantCoeff_eq] using hp

theorem centerPolynomial_intertwines {n : ℕ} (r : PositiveRoot n) (p : MatrixPolynomial n) :
    matrixUnitDerivation r.val.1 r.val.2 (centerPolynomial n p) =
      centerPolynomial n (centeredRootDerivative r p) := by
  have hX (ij : Fin n × Fin n) :
      matrixUnitDerivation r.val.1 r.val.2 (centerPolynomial n (X ij)) =
        centerPolynomial n (centeredRootDerivative r (X ij)) := by
    rcases ij with ⟨i,j⟩
    simp only [centerPolynomial, aeval_X, map_sub, derivation_C, sub_zero,
      centeredRootDerivative, Derivation.add_apply, matrixUnitDerivation_X,
      pderiv_X, Pi.single_apply, rootCoordinate, map_add]
    by_cases hi : i = r.val.2
    · subst i
      by_cases hj : j = r.val.1
      · subst j; simp
      · simp [hj, Ne.symm hj]
    · simp [hi, Ne.symm hi]
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p ij hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, hp, hX, map_add]

theorem centerPolynomial_word {n : ℕ} (w : List (PositiveRoot n)) (p : MatrixPolynomial n) :
    polynomialEnveloping n (rootWord w) (centerPolynomial n p) =
      centerPolynomial n
        (differentialWord (fun r => (centeredRootDerivative r).toLinearMap) w p) := by
  induction w with
  | nil => simp [rootWord]
  | cons r w ih =>
    rw [rootWord_cons, map_mul, Module.End.mul_apply, ih, polynomialEnveloping_root,
      differentialWord_cons, Module.End.mul_apply]
    exact centerPolynomial_intertwines r _

theorem rootWord_principal {n : ℕ} (w : List (PositiveRoot n))
    (p : MatrixPolynomial n) (hp : p ∈ jet w.length) :
    evaluateIdentity n (polynomialEnveloping n (rootWord w) (centerPolynomial n p)) =
      coeff 0 (differentialWord (fun r => (pderiv (rootCoordinate r)).toLinearMap) w p) := by
  rw [centerPolynomial_word, evaluateIdentity_center]
  exact differentialWord_principal _ rootCoordinate centeredRootDerivative_lowers
    centeredRootDerivative_error w hp

theorem rootWord_constant_zero {n : ℕ} (w : List (PositiveRoot n))
    (p : MatrixPolynomial n) (hp : p ∈ jet (w.length+1)) :
    evaluateIdentity n (polynomialEnveloping n (rootWord w) (centerPolynomial n p)) = 0 := by
  rw [centerPolynomial_word, evaluateIdentity_center]
  exact differentialWord_constant_zero _ centeredRootDerivative_lowers w hp

end
end Schubert.RS.Representation
