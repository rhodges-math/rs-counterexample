import Schubert.RS.Complexity.Decision
import Schubert.RS.Complexity.RationalFeasibility
import Schubert.RS.GL.CharacterMultiplicity
import Schubert.RS.Quiver.Polytope.Counts
import Schubert.RS.Quiver.Saturation

/-!
# Corollaries of the endpoints applied to proofs of the statements in `Statements/`

Some endpoints in the other `Main` files take a statement of `Schubert/RS/Statements/` as a
hypothesis. Applied to a proof of that statement, each gives a corollary without that hypothesis;
such corollaries are recorded here, each as a one-line application of the endpoint.

* `PolyTimeRationalFeasibility` (`Schubert.RS.polyTimeRationalFeasibility_holds`):
  `Schubert.RS.Algorithms.quiverPositivity_decision_of_criterion` and
  `Schubert.RS.Algorithms.quiverPositivity_decision_of_saturation`.
* `GLCharacterMultiplicity` (`Schubert.RS.glCharacterMultiplicity_holds`):
  `Schubert.RS.Quiver.ForwardQuiver.finrank_ratLeviIrrep_coordRep_eq_multiplicity`,
  `Schubert.RS.Quiver.atomCoefficient_eq_finrank_quiverHom` (Theorem 5.3) and
  `Schubert.RS.Quiver.Flat.quiverTheorem_identity` (Theorem 1.4, the displayed identity).
* `QuiverSaturation` (`Schubert.RS.quiverSaturation_holds`):
  `Schubert.RS.Algorithms.quiverPositivity_decision_polyTime` (Theorem 1.4, decision),
  `Schubert.RS.Quiver.ForwardQuiver.multiplicity_pos_of_nsmul_pos`,
  `Schubert.RS.Quiver.Flat.quiverCoefficient_pos_iff_realPoint` and
  `Schubert.RS.Quiver.Flat.quiverCoefficient_pos_iff_ratPoint` (Theorem 1.4, positivity).
-/

namespace Schubert.RS.Algorithms

open Complexity Schubert.RS.Quiver.Flat

/-- `quiverPositivity_decision_of_iff` applied to `polyTimeRationalFeasibility_holds`: given the
positivity criterion for quiver triples, some polynomial-time function accepts the encoding of
`(a, b, c)` exactly when `(a, b, c)` is a quiver triple with `[𝒜_c](κ_a κ_b) > 0`. -/
theorem quiverPositivity_decision_of_criterion
    (hpos : ∀ a b c : List ℕ, IsQuiverTripleList a b c →
      (0 < atomCoefficientList a b c ↔ (quiverPolytope a b c).RatFeasible)) :
    ∃ f ∈ FP, ∀ a b c : List ℕ,
      f (encodeTriple a b c) = [true] ↔
        IsQuiverTripleList a b c ∧ 0 < atomCoefficientList a b c :=
  quiverPositivity_decision_of_iff hpos polyTimeRationalFeasibility_holds

/-- `quiverPositivity_decision` applied to `polyTimeRationalFeasibility_holds` (Theorem 1.4,
decision): given `QuiverSaturation`, some polynomial-time function accepts the encoding of
`(a, b, c)` exactly when `(a, b, c)` is a quiver triple with `[𝒜_c](κ_a κ_b) > 0`. -/
theorem quiverPositivity_decision_of_saturation (hsat : QuiverSaturation) :
    ∃ f ∈ FP, ∀ a b c : List ℕ,
      f (encodeTriple a b c) = [true] ↔
        IsQuiverTripleList a b c ∧ 0 < atomCoefficientList a b c :=
  quiverPositivity_decision hsat polyTimeRationalFeasibility_holds

/-- `quiverPositivity_decision_of_saturation` applied to `quiverSaturation_holds` (Theorem 1.4,
decision): some polynomial-time function accepts the encoding of `(a, b, c)` exactly when
`(a, b, c)` is a quiver triple with `[𝒜_c](κ_a κ_b) > 0`. -/
theorem quiverPositivity_decision_polyTime :
    ∃ f ∈ FP, ∀ a b c : List ℕ,
      f (encodeTriple a b c) = [true] ↔
        IsQuiverTripleList a b c ∧ 0 < atomCoefficientList a b c :=
  quiverPositivity_decision_of_saturation quiverSaturation_holds

end Schubert.RS.Algorithms

namespace Schubert.RS.Quiver

/-- `ForwardQuiver.finrank_intertwiningMap_coordRep_eq_multiplicity_of` applied to
`glCharacterMultiplicity_holds`: for every forward quiver `Q` and dominant weight `λ`,
`dim Hom_L(V^λ, R_Q)` is the multiplicity of `λ` in the characters of the graded pieces. -/
theorem ForwardQuiver.finrank_ratLeviIrrep_coordRep_eq_multiplicity (Q : ForwardQuiver)
    (lam : (p : Fin Q.s) → TauCeti.DominantWeight (Q.dim p)) :
    (Module.finrank ℂ ((GL.ratLeviIrrep Q.dim lam).IntertwiningMap Q.coordRep) : ℤ) =
      Q.multiplicity fun p => (lam p).1 :=
  Q.finrank_intertwiningMap_coordRep_eq_multiplicity_of glCharacterMultiplicity_holds lam

/-- `atomCoefficient_eq_finrank_hom` applied to `glCharacterMultiplicity_holds` (Theorem 5.3,
`thm:quiver-coefficient`): for a quiver partition `I` of `(a, b, c)`,
`[𝒜_c](κ_a κ_b) = dim Hom_{L_I}(⊗_p V_p^{λ^{(p)}}, R_Q)`. -/
theorem atomCoefficient_eq_finrank_quiverHom {n : ℕ} {a b c : Composition n} {N : ℕ}
    {I : IntervalPartition n} (h : IsQuiverPartition a b c N I) :
    atomCoefficient (key a * key b) c =
      Module.finrank ℂ ((GL.ratLeviIrrep (quiverOf a b c N I).dim
        (leviDominantWeight h)).IntertwiningMap (quiverOf a b c N I).coordRep) :=
  atomCoefficient_eq_finrank_hom glCharacterMultiplicity_holds h

/-- `quiverTheorem_counts` applied to `glCharacterMultiplicity_holds` (Theorem 1.4, the displayed
identity): for a quiver triple, with the canonical partition `I`, `N = max c` and the quiver `Q`
of Theorem 5.3, the space `Hom_{L_I}(⊗_p V_p^{λ^{(p)}}, R_Q)` is finite-dimensional,
`[𝒜_c](κ_a κ_b) = dim Hom_{L_I}(⊗_p V_p^{λ^{(p)}}, R_Q) = #(P(a, b, c) ∩ ℤ^M)`, and
`P(a, b, c) ∩ ℤ^M` is finite. -/
theorem Flat.quiverTheorem_identity {a b c : List ℕ}
    (h : IsQuiverTriple (Flat.listComp c.length a) (Flat.listComp c.length b)
      (Flat.listComp c.length c)) :
    FiniteDimensional ℂ ((GL.ratLeviIrrep (Flat.canonicalQuiver a b c).dim
      (Flat.canonicalDominantWeight h)).IntertwiningMap (Flat.canonicalQuiver a b c).coordRep) ∧
    atomCoefficient (key (Flat.listComp c.length a) * key (Flat.listComp c.length b))
        (Flat.listComp c.length c) =
      Module.finrank ℂ ((GL.ratLeviIrrep (Flat.canonicalQuiver a b c).dim
        (Flat.canonicalDominantWeight h)).IntertwiningMap
          (Flat.canonicalQuiver a b c).coordRep) ∧
    atomCoefficient (key (Flat.listComp c.length a) * key (Flat.listComp c.length b))
        (Flat.listComp c.length c) = Nat.card (Flat.quiverPolytope a b c).intPoints ∧
      (Flat.quiverPolytope a b c).intPoints.Finite :=
  Flat.quiverTheorem_counts glCharacterMultiplicity_holds h

/-- `ForwardQuiver.multiplicity_pos_of_nsmul` applied to `quiverSaturation_holds`: for a dominant
weight `λ` and `N ≥ 1`, positivity of the multiplicity of `N λ` implies positivity for `λ`. -/
theorem ForwardQuiver.multiplicity_pos_of_nsmul_pos (Q : ForwardQuiver) {lam : Q.Weight}
    (hlam : Q.IsDominant lam) {N : ℕ} (hN : 0 < N) (h : 0 < Q.multiplicity (N • lam)) :
    0 < Q.multiplicity lam :=
  Q.multiplicity_pos_of_nsmul quiverSaturation_holds hlam hN h

/-- `Flat.quiverCoefficient_pos_iff_nonempty` applied to `quiverSaturation_holds` (Theorem 1.4,
positivity): for a quiver triple, `[𝒜_c](κ_a κ_b) > 0` iff the polytope `P(a, b, c) ⊆ ℝ^M` is
nonempty. -/
theorem Flat.quiverCoefficient_pos_iff_realPoint {a b c : List ℕ}
    (h : IsQuiverTriple (Flat.listComp c.length a) (Flat.listComp c.length b)
      (Flat.listComp c.length c)) :
    0 < atomCoefficient (key (Flat.listComp c.length a) * key (Flat.listComp c.length b))
        (Flat.listComp c.length c) ↔ ((Flat.quiverPolytope a b c).points ℝ).Nonempty :=
  Flat.quiverCoefficient_pos_iff_nonempty quiverSaturation_holds h

/-- `Flat.quiverCoefficient_pos_iff_ratFeasible` applied to `quiverSaturation_holds` (Theorem 1.4,
positivity, rational form): for a quiver triple, `[𝒜_c](κ_a κ_b) > 0` iff the system
`P(a, b, c)` has a rational solution. -/
theorem Flat.quiverCoefficient_pos_iff_ratPoint {a b c : List ℕ}
    (h : IsQuiverTriple (Flat.listComp c.length a) (Flat.listComp c.length b)
      (Flat.listComp c.length c)) :
    0 < atomCoefficient (key (Flat.listComp c.length a) * key (Flat.listComp c.length b))
        (Flat.listComp c.length c) ↔ (Flat.quiverPolytope a b c).RatFeasible :=
  Flat.quiverCoefficient_pos_iff_ratFeasible quiverSaturation_holds h

end Schubert.RS.Quiver
