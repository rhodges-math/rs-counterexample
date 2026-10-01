import Schubert.RS.Complexity.Recognition
import Schubert.RS.Complexity.Decision
import Schubert.RS.Complexity.TwoSourceAlgorithm
import Schubert.RS.Complexity.Sanity
import Schubert.RS.Statements.PolyTimeRationalFeasibility

/-!
# Endpoints: Theorem 1.4 and Proposition 5.8, complexity

Polynomial time is complexitylib's `Complexity.FP`, computed by deterministic multi-tape Turing
machines. Inputs are encoded with `Complexity.DataEncode.bitstringEncode`, with natural numbers
in binary.

Namespace `Schubert.RS.Algorithms`:
* Input encoding: `encodeTriple a b c`. Its length is linear in the binary size of the input
  (`binarySize_le_length`, `length_le_binarySize`).
* Lists as compositions: `toComposition`, `IsQuiverTripleList`, `atomCoefficientList`.
* Recognition of quiver triples: `quiverTriple_recognition`. Some polynomial-time function
  outputs `isQuiverTripleListBool a b c` (`isQuiverTripleListBool_iff`) on the encoding of every
  input. The test is the paper's recognition argument in the arithmetic form
  `isQuiverTripleList_iff_listConditions`.
* Construction of the polytope: `quiverPolytope_construction`. Some polynomial-time function maps
  the encoding of every triple of lists to the encoding of `Quiver.Flat.quiverPolytope a b c`
  (its dimension and its rows). Its description has polynomial size (`quiverPolytope_size`).
* The positivity decision: `quiverPositivity_decision`. Given `QuiverSaturation` and
  `PolyTimeRationalFeasibility`, some polynomial-time function accepts the encoding of `(a, b, c)`
  exactly when it is a quiver triple with `[𝒜_c](κ_a κ_b) > 0`. The algorithm
  (`quiverPositivity_decision_of_iff`, which takes `PolyTimeRationalFeasibility` as a hypothesis,
  and the positivity criterion for quiver triples as a second one) recognizes the triple,
  constructs `P(a, b, c)` and tests it for a rational point.
* Proposition 5.8 (last sentence): `twoSource_coefficient_computable`. Some polynomial-time
  function maps the unary encoding `encodeTripleUnary` of every triple satisfying the hypotheses
  of Proposition 5.8 to the encoding of the integer `[𝒜_c](κ_a κ_b)`. The unary encoding is
  injective (`encodeTripleUnary_injective`) and has length `4 (|a| + |b| + |c|) + 6 n + 8`
  (`length_encodeTripleUnary_ofFn`), so polynomial time in it is polynomial time in
  `n + |a| + |b| + |c|`. The algorithm is the dynamic program `twoSourceCount`
  (`twoSource_eq_count`), on binary values.
* Sanity checks that the complexity classes are non-trivial: `Complexity.FP` and `Complexity.P`
  are countable, so some function and some language lie outside them (`exists_not_mem_FP`,
  `exists_not_mem_P`); and by the time hierarchy theorem, for every `a ≥ 1` some language in
  `Complexity.P` is not decidable in time `O(n^a)` (`exists_mem_P_not_mem_DTIME`).

Statements used as hypotheses (namespace `Schubert.RS`, folder `Statements/`):
`PolyTimeRationalFeasibility` and `QuiverSaturation`.
-/
