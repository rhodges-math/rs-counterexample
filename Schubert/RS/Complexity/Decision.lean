import Schubert.RS.Complexity.Decide
import Schubert.RS.Quiver.Polytope.Positivity

/-!
# Deciding positivity of quiver coefficients in polynomial time

Theorem 1.4 (decision): whether `(a, b, c)` is a quiver triple with `[𝒜_c](κ_a κ_b) > 0` can be
decided in time polynomial in the binary length of the input, given `QuiverSaturation` and
`PolyTimeRationalFeasibility`. The algorithm recognizes quiver triples, constructs `P(a, b, c)` and
tests whether it has a rational point; `QuiverSaturation` gives the criterion
`[𝒜_c](κ_a κ_b) > 0 ⇔ P(a, b, c)` has a rational point
(`Quiver.Flat.quiverCoefficient_pos_iff_ratFeasible`).
-/

namespace Schubert.RS.Algorithms

open Complexity

/-- **Theorem 1.4 (decision).** Given `QuiverSaturation` and `PolyTimeRationalFeasibility`, some
polynomial-time function accepts the encoding of `(a, b, c)` (natural numbers in binary) exactly
when `(a, b, c)` is a quiver triple with `[𝒜_c](κ_a κ_b) > 0`. -/
theorem quiverPositivity_decision (hsat : QuiverSaturation) (hlp : PolyTimeRationalFeasibility) :
    ∃ f ∈ FP, ∀ a b c : List ℕ,
      f (encodeTriple a b c) = [true] ↔
        IsQuiverTripleList a b c ∧ 0 < atomCoefficientList a b c :=
  quiverPositivity_decision_of_iff
    (fun _ _ _ h => Quiver.Flat.quiverCoefficient_pos_iff_ratFeasible hsat h.2.2) hlp

end Schubert.RS.Algorithms
