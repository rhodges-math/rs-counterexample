import Schubert.RS.Quiver.HomSpace
import Schubert.RS.Quiver.Polytope.Lattice

/-!
# Theorem 1.4: the counting identity

For a quiver triple `(a, b, c)` (lists, padded with zeros to the length `n` of `c`), with the
canonical partition `I` and `N = max c`, the quiver `Q` of Theorem 5.3 and the polytope
`P(a, b, c)` of Theorem 1.4:

  `[𝒜_c](κ_a κ_b) = dim Hom_{L_I}(⊗_p V_p^{λ^{(p)}}, R_Q) = #(P(a, b, c) ∩ ℤ^M)`,

and `P(a, b, c)` has finitely many integer points. The first equality takes the statement
`GLCharacterMultiplicity` as a hypothesis (`quiverTheorem_counts`); the outer equality does not
(`quiverPolytope_card`).

## Main results

* `Schubert.RS.Quiver.Flat.quiverPolytope_card`
* `Schubert.RS.Quiver.Flat.quiverTheorem_counts`
* `Schubert.RS.Quiver.Flat.finiteDimensional_canonicalHom`
-/

namespace Schubert.RS.Quiver.Flat

open Schubert.RS.GL

variable {a b c : List ℕ}

/-- For a quiver triple, the canonical partition is a quiver partition, with `N = max c`. -/
theorem isQuiverPartition_canonicalPart
    (h : IsQuiverTriple (listComp c.length a) (listComp c.length b) (listComp c.length c)) :
    IsQuiverPartition (listComp c.length a) (listComp c.length b) (listComp c.length c)
      (Finset.univ.sup (listComp c.length c)) (canonicalPart a b c) :=
  isQuiverTriple_iff_canonical.mp h

/-- The weights `λ^{(p)}` of the canonical quiver of a quiver triple, as dominant weights: the
highest weights of the irreducible representations `V_p^{λ^{(p)}}`. -/
def canonicalDominantWeight
    (h : IsQuiverTriple (listComp c.length a) (listComp c.length b) (listComp c.length c)) :
    (p : Fin (canonicalQuiver a b c).s) → TauCeti.DominantWeight ((canonicalQuiver a b c).dim p) :=
  leviDominantWeight (isQuiverPartition_canonicalPart h)

/-- **Theorem 1.4, the counting identity** `[𝒜_c](κ_a κ_b) = #(P(a, b, c) ∩ ℤ^M)` for a quiver
triple, and the polytope has finitely many integer points. -/
theorem quiverPolytope_card
    (h : IsQuiverTriple (listComp c.length a) (listComp c.length b) (listComp c.length c)) :
    atomCoefficient (key (listComp c.length a) * key (listComp c.length b))
        (listComp c.length c) = Nat.card (quiverPolytope a b c).intPoints ∧
      (quiverPolytope a b c).intPoints.Finite :=
  ⟨atomCoefficient_eq_card_intPoints a b c h, finite_intPoints a b c h⟩

/-- The space `Hom_{L_I}(⊗_p V_p^{λ^{(p)}}, R_Q)` for the canonical quiver of a quiver triple is
finite-dimensional. -/
theorem finiteDimensional_canonicalHom
    (h : IsQuiverTriple (listComp c.length a) (listComp c.length b) (listComp c.length c)) :
    FiniteDimensional ℂ ((ratLeviIrrep (canonicalQuiver a b c).dim
      (canonicalDominantWeight h)).IntertwiningMap (canonicalQuiver a b c).coordRep) :=
  finiteDimensional_quiverHom (isQuiverPartition_canonicalPart h)

/-- **Theorem 1.4, the displayed identity**, given `GLCharacterMultiplicity` as a hypothesis: for
a quiver triple, with the canonical partition `I`, `N = max c` and the quiver `Q` of Theorem 5.3,
the space `Hom_{L_I}(⊗_p V_p^{λ^{(p)}}, R_Q)` is finite-dimensional,
`[𝒜_c](κ_a κ_b) = dim Hom_{L_I}(⊗_p V_p^{λ^{(p)}}, R_Q) = #(P(a, b, c) ∩ ℤ^M)`, and
`P(a, b, c) ∩ ℤ^M` is finite. -/
theorem quiverTheorem_counts (hgl : GLCharacterMultiplicity)
    (h : IsQuiverTriple (listComp c.length a) (listComp c.length b) (listComp c.length c)) :
    FiniteDimensional ℂ ((ratLeviIrrep (canonicalQuiver a b c).dim
      (canonicalDominantWeight h)).IntertwiningMap (canonicalQuiver a b c).coordRep) ∧
    atomCoefficient (key (listComp c.length a) * key (listComp c.length b))
        (listComp c.length c) =
      Module.finrank ℂ ((ratLeviIrrep (canonicalQuiver a b c).dim
        (canonicalDominantWeight h)).IntertwiningMap (canonicalQuiver a b c).coordRep) ∧
    atomCoefficient (key (listComp c.length a) * key (listComp c.length b))
        (listComp c.length c) = Nat.card (quiverPolytope a b c).intPoints ∧
      (quiverPolytope a b c).intPoints.Finite :=
  ⟨finiteDimensional_canonicalHom h,
    atomCoefficient_eq_finrank_hom hgl (isQuiverPartition_canonicalPart h), quiverPolytope_card h⟩

end Schubert.RS.Quiver.Flat
