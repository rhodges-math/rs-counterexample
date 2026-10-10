import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.BigOperators.Fin

/-!
# Systems of linear inequalities with integer coefficients

A finite system `A x ≤ b` with integer coefficients, given by its rows, and its solutions over an
ordered field. This is the input format of the feasibility statement
`Schubert.RS.PolyTimeRationalFeasibility`. A rational system has an integral description (clear
denominators row by row), so integer data loses nothing.

## Main definitions

* `Schubert.RS.IntPolyhedron`: the number of variables and the rows `(a, β)` of `a · x ≤ β`.
* `Schubert.RS.IntPolyhedron.Satisfies`: a point satisfies every row.
* `Schubert.RS.IntPolyhedron.RatFeasible`: the system has a rational solution.
-/

namespace Schubert.RS

/-- A finite system of linear inequalities `a · x ≤ β` with integer coefficients in `dim`
variables. A row is a dense coefficient list `a` (missing entries are `0`, entries beyond `dim` are
ignored) together with its right-hand side `β`. -/
structure IntPolyhedron where
  /-- The number of variables. -/
  dim : ℕ
  /-- The rows `(a, β)` of the inequalities `a · x ≤ β`. -/
  rows : List (List ℤ × ℤ)

namespace IntPolyhedron

variable (P : IntPolyhedron) {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The value `a · x` of a coefficient row at a point. -/
def rowValue (a : List ℤ) (x : Fin P.dim → K) : K :=
  ∑ i : Fin P.dim, (a.getD i 0 : K) * x i

/-- The point `x` satisfies every inequality of the system. -/
def Satisfies (x : Fin P.dim → K) : Prop :=
  ∀ r ∈ P.rows, P.rowValue r.1 x ≤ (r.2 : K)

/-- The system has a rational solution. -/
def RatFeasible : Prop :=
  ∃ x : Fin P.dim → ℚ, P.Satisfies x

end IntPolyhedron

end Schubert.RS
