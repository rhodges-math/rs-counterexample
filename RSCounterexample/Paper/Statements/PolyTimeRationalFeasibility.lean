import RSCounterexample.Paper.Complexity.Instances
import Complexitylib.Classes.P.Defs

/-!
# Polynomial-time feasibility of systems of linear inequalities

STATUS: proved in this library: `Schubert.RS.polyTimeRationalFeasibility_holds`
(`RSCounterexample/Paper/Complexity/RationalFeasibility.lean`, from the library `RSCounterexample/LinearProgramming`).

Whether a finite system of linear inequalities with integer coefficients has a rational solution
can be decided in time polynomial in the binary size of the system: L. G. Khachiyan, *A polynomial
algorithm in linear programming*, Dokl. Akad. Nauk SSSR 244 (1979); for systems whose
coefficients are small in absolute value even in strongly polynomial time, É. Tardos, *A strongly
polynomial algorithm to solve combinatorial linear programs*, Oper. Res. 34 (1986).

Polynomial time is complexitylib's `Complexity.FP` (deterministic multi-tape Turing machines), and
the inputs are encoded by `Complexity.DataEncode.bitstringEncode` with the instances of
`Schubert.RS.Algorithms` (sign and binary magnitude for integers).
-/

open Schubert.RS.Algorithms

namespace Schubert.RS

/-- **Feasibility of integer linear systems is decidable in polynomial time.** Some
polynomial-time function on bitstrings accepts exactly the encodings of the finite systems
`A x ≤ b` with integer coefficients that have a rational solution. -/
def PolyTimeRationalFeasibility : Prop :=
  ∃ f : List Bool → List Bool, f ∈ Complexity.FP ∧
    ∀ P : IntPolyhedron, f (Complexity.DataEncode.bitstringEncode P) = [true] ↔ P.RatFeasible

end Schubert.RS
