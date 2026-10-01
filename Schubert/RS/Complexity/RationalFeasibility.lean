import Schubert.RS.Statements.PolyTimeRationalFeasibility
import Schubert.LinearProgramming.Feasibility

/-!
# Polynomial-time feasibility of systems of linear inequalities

This file proves the statement `Schubert.RS.PolyTimeRationalFeasibility`
(`Schubert.RS.polyTimeRationalFeasibility_holds`) from the main theorem
`LinearProgramming.exists_mem_FP_feasible` of the library `Schubert/LinearProgramming`.

The encoding `Complexity.DataEncode.bitstringEncode P` of a system `P : IntPolyhedron` with the
instances of `Schubert.RS.Algorithms` (integers as sign and binary absolute value, a system as
its dimension and its rows) is the library's `LinearProgramming.encodeSystem P.dim P.rows`
(`Schubert.RS.bitstringEncode_eq_encodeSystem`). Rational feasibility of `P` is the library's
`LinearProgramming.SystemFeasible P.dim P.rows`
(`Schubert.RS.IntPolyhedron.ratFeasible_iff_systemFeasible`). Both conventions treat the
coefficient lists the same way: missing coefficients are `0`, and coefficients beyond `dim` are
ignored. The library reduces to the `min dim (longest row)` variables that matter, so a binary
`dim` far larger than every row is handled in polynomial time.

## Main results

* `Schubert.RS.polyTimeRationalFeasibility_holds`: the statement holds.
-/

namespace Schubert.RS

open Schubert.RS.Algorithms

/-- The encoding of a system is the library's encoding of its dimension and rows. -/
theorem bitstringEncode_eq_encodeSystem (P : IntPolyhedron) :
    Complexity.DataEncode.bitstringEncode P = LinearProgramming.encodeSystem P.dim P.rows :=
  rfl

/-- Rational feasibility is the library's feasibility of the dimension and the rows. -/
theorem IntPolyhedron.ratFeasible_iff_systemFeasible (P : IntPolyhedron) :
    P.RatFeasible ↔ LinearProgramming.SystemFeasible P.dim P.rows :=
  Iff.rfl

/-- **Feasibility of integer linear systems is decidable in polynomial time**: the statement
`Schubert.RS.PolyTimeRationalFeasibility` holds. -/
theorem polyTimeRationalFeasibility_holds : PolyTimeRationalFeasibility := by
  obtain ⟨f, hf, hspec⟩ := LinearProgramming.exists_mem_FP_feasible
  exact ⟨f, hf, fun P => by
    rw [bitstringEncode_eq_encodeSystem, hspec, IntPolyhedron.ratFeasible_iff_systemFeasible]⟩

end Schubert.RS
