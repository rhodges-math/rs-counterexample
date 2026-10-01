import Schubert.RS.Complexity.Construction
import Schubert.RS.Complexity.Recognition
import Schubert.RS.Statements.PolyTimeRationalFeasibility

/-!
# Size of the polytope and the positivity decision

* `quiverPolytope_size`: the description of `P(a, b, c)` has size polynomial in the
  binary length of the input, since it is computed in polynomial time.
* `quiverPositivity_decision_of_iff`: the algorithm of Theorem 1.4 that decides
  `[𝒜_c](κ_a κ_b) > 0`. It recognizes quiver triples, constructs `P(a, b, c)` and tests it for
  feasibility with a polynomial-time feasibility test (`PolyTimeRationalFeasibility`). Its
  correctness rests on the criterion `[𝒜_c](κ_a κ_b) > 0 ⇔ P(a, b, c)` has a rational point, for
  quiver triples, taken here as the hypothesis `hpos`.
-/

namespace Schubert.RS.Algorithms

open Complexity Schubert.RS.Quiver.Flat

noncomputable section

/-- **The description of `P(a, b, c)` has polynomial size**: the length of its encoding is bounded
by a polynomial in the length of the encoding of `(a, b, c)`. -/
theorem quiverPolytope_size :
    ∃ p : _root_.Polynomial ℕ, ∀ a b c : List ℕ,
      (DataEncode.bitstringEncode (quiverPolytope a b c)).length ≤
        p.eval (encodeTriple a b c).length := by
  obtain ⟨f, hf, hfeq⟩ := quiverPolytope_construction
  obtain ⟨p, hp⟩ := Cobham.output_length_poly_of_mem_FP hf
  exact ⟨p, fun a b c => hfeq a b c ▸ hp _⟩

/-- **The positivity decision**, from the positivity criterion for quiver triples. If, for every
quiver triple, `[𝒜_c](κ_a κ_b) > 0` exactly when `P(a, b, c)` has a rational point, and
feasibility of integer linear systems is decidable in polynomial time, then some polynomial-time
function accepts the encoding of `(a, b, c)` exactly when `(a, b, c)` is a quiver triple with
`[𝒜_c](κ_a κ_b) > 0`. -/
theorem quiverPositivity_decision_of_iff
    (hpos : ∀ a b c : List ℕ, IsQuiverTripleList a b c →
      (0 < atomCoefficientList a b c ↔ (quiverPolytope a b c).RatFeasible))
    (hlp : PolyTimeRationalFeasibility) :
    ∃ f ∈ FP, ∀ a b c : List ℕ,
      f (encodeTriple a b c) = [true] ↔
        IsQuiverTripleList a b c ∧ 0 < atomCoefficientList a b c := by
  obtain ⟨r, hr, hreq⟩ := quiverTriple_recognition
  obtain ⟨k, hk, hkeq⟩ := quiverPolytope_construction
  obtain ⟨g, hg, hgeq⟩ := hlp
  have hp : FPPred fun z => (r z)[0]?.getD false = true := FPPred.getBit hr (UnaryFn.const 0)
  refine ⟨fun z => if (r z)[0]?.getD false = true then g (k z) else [false],
    FPPred.ite_mem_FP hp (mem_FP_comp hk hg) (constFn_mem_FP [false]), fun a b c => ?_⟩
  simp only [hreq, hkeq]
  by_cases h : IsQuiverTripleList a b c
  · have hb : isQuiverTripleListBool a b c = true := (isQuiverTripleListBool_iff a b c).mpr h
    simp only [hb, List.getElem?_cons_zero, Option.getD_some, ite_true]
    rw [hgeq, hpos a b c h]
    exact ⟨fun h' => ⟨h, h'⟩, fun h' => h'.2⟩
  · have hb : isQuiverTripleListBool a b c = false := by
      rw [Bool.eq_false_iff]
      exact fun h' => h ((isQuiverTripleListBool_iff a b c).mp h')
    simp [hb, h]

end

end Schubert.RS.Algorithms
