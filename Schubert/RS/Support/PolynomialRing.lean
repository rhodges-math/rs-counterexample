import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Only the polynomial-ring abbreviation needed by divided differences.
There is no quotient, cohomology ring, restriction map, or kernel theorem. -/
namespace Schubert.BorelPresentation
abbrev PolynomialRing (n : ℕ) := MvPolynomial (Fin n) ℤ
end Schubert.BorelPresentation
