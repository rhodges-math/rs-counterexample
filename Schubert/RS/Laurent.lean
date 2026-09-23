import Schubert.RS.Operators
import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-!
# Finite Laurent polynomials and the ordinary-polynomial embedding

The root-cone series used later are separate from this finite Laurent algebra.
No rational-function division is built into coefficient extraction.
-/

namespace Schubert.RS

noncomputable section
variable {n : ℕ}

abbrev Weight (n : ℕ) := Fin n → ℤ
abbrev Laurent (n : ℕ) := AddMonoidAlgebra ℤ (Weight n)

/-- Embed a polynomial exponent into the integer weight lattice. -/
def exponentWeight : (Fin n →₀ ℕ) →+ Weight n where
  toFun a i := a i
  map_zero' := by funext i; simp
  map_add' a b := by funext i; simp

theorem exponentWeight_injective : Function.Injective (exponentWeight (n := n)) := by
  intro a b h
  ext i
  have hi := congrFun h i
  change (a i : ℤ) = (b i : ℤ) at hi
  exact_mod_cast hi

/-- The actual injective ring map from ordinary to Laurent polynomials. -/
def toLaurent : Polynomial n →+* Laurent n :=
  AddMonoidAlgebra.mapDomainRingHom ℤ exponentWeight

theorem toLaurent_injective : Function.Injective (toLaurent (n := n)) :=
  AddMonoidAlgebra.mapDomain_injective exponentWeight_injective

@[simp] theorem toLaurent_monomial (a : Fin n →₀ ℕ) (z : ℤ) :
    toLaurent (MvPolynomial.monomial a z) =
      AddMonoidAlgebra.single (exponentWeight a) z := by
  exact AddMonoidAlgebra.mapDomain_single

def constantTerm (p : Laurent n) : ℤ := p.coeff 0

@[simp] theorem constantTerm_add (p q : Laurent n) :
    constantTerm (p + q) = constantTerm p + constantTerm q := by
  simp [constantTerm]

@[simp] theorem constantTerm_sub (p q : Laurent n) :
    constantTerm (p - q) = constantTerm p - constantTerm q := by
  simp [constantTerm]

theorem constantTerm_monomial_mul (a : Weight n) (p : Laurent n) :
    constantTerm (AddMonoidAlgebra.single a 1 * p) = p.coeff (-a) := by
  simp [constantTerm]

/-- Shifting by a monomial does not discard any coefficient. -/
theorem laurent_coefficient_shift (a b : Weight n) (p : Laurent n) :
    (AddMonoidAlgebra.single a 1 * p).coeff (a + b) = p.coeff b := by
  simp

def positiveRoot (i j : Fin n) : Weight n := Pi.single i 1 - Pi.single j 1

/-- The finite Weyl denominator in the manuscript's upper-root convention. -/
def weylFactor (n : ℕ) : Laurent n :=
  ∏ i : Fin n, ∏ j ∈ Finset.univ.filter (i < ·),
    (1 - AddMonoidAlgebra.single (positiveRoot i j) 1)

end
end Schubert.RS
