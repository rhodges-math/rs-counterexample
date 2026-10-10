import RSCounterexample.Paper.Quiver.Polytope.LatticeEquiv
import RSCounterexample.Paper.Quiver.Polytope.LatticeTriple
import RSCounterexample.Paper.Quiver.Extraction

/-!
# The lattice-point identity

For lists `a, b, c` (weak compositions of length `n = c.length`, padded with zeros), the integer
points of the polytope `P(a, b, c)` of Theorem 1.4 count the coefficient of the atom `𝒜_c` in
`κ_a κ_b`:

  `[𝒜_c](κ_a κ_b) = #(P(a, b, c) ∩ ℤ^M)` for every quiver triple
  (`Schubert.RS.Quiver.Flat.atomCoefficient_eq_card_intPoints`).

More generally, for any weight `w` that agrees at the vertices with a dominant weight `λ` of the
canonical quiver `Q` of the triple, the integer points of the polytope of `positionalOf a b c` with
weight `w` are in bijection with the arrow shapes with LR chains ending at `λ`
(`Schubert.RS.Quiver.Flat.intPointsEquiv`), so their number is the multiplicity of `λ` in the
coordinate ring of the quiver (`Schubert.RS.Quiver.Flat.multiplicity_eq_card_intPoints`). The
bijection holds for all lists; the hypothesis that `(a, b, c)` is a quiver triple enters only
through Theorem 5.3 (`Schubert.RS.Quiver.atomCoefficient_eq_multiplicity`) and the dominance of
the weight of the quiver.

## Main results

* `Schubert.RS.Quiver.Flat.intPointsEquiv`
* `Schubert.RS.Quiver.Flat.multiplicity_eq_card_intPoints`,
  `Schubert.RS.Quiver.Flat.finite_intPoints_withWeight`
* `Schubert.RS.Quiver.Flat.atomCoefficient_eq_card_intPoints`,
  `Schubert.RS.Quiver.Flat.finite_intPoints`
-/

namespace Schubert.RS.Quiver.Flat

variable (a b c : List ℕ)

/-- **The integer points of the polytope are the arrow shapes with LR chains**, for the polytope of
`positionalOf a b c` with any weight `w` that agrees with the weight `λ` of the canonical quiver at
its vertices. -/
noncomputable def intPointsEquiv (w : ℕ → ℕ → ℤ) (lam : (canonicalQuiver a b c).Weight)
    (hw : ∀ p (l : Fin ((canonicalQuiver a b c).dim p)),
      w ((canonicalPart a b c).first p) l = lam p l) :
    ((positionalOf a b c).withWeight w).polytope.intPoints ≃
      Σ μ : (canonicalQuiver a b c).ArrowShapes, (canonicalQuiver a b c).VertexChains μ lam :=
  (Equiv.subtypeEquivRight fun z =>
    PositionalQuiver.mem_intPoints_iff (wellFormed_positionalOf a b c w) z).trans
    (realizes_positionalOf a b c w lam hw).conditionsEquiv

/-- For a dominant weight, the polytope has finitely many integer points. -/
theorem finite_intPoints_withWeight (w : ℕ → ℕ → ℤ) (lam : (canonicalQuiver a b c).Weight)
    (hlam : (canonicalQuiver a b c).IsDominant lam)
    (hw : ∀ p (l : Fin ((canonicalQuiver a b c).dim p)),
      w ((canonicalPart a b c).first p) l = lam p l) :
    ((positionalOf a b c).withWeight w).polytope.intPoints.Finite := by
  have := (canonicalQuiver a b c).finite_chains hlam
  exact Set.finite_coe_iff.mp (Finite.of_equiv _ (intPointsEquiv a b c w lam hw).symm)

/-- **The multiplicity is the number of integer points**: for a dominant weight `λ` of the
canonical quiver and any weight `w` agreeing with `λ` at the vertices, the multiplicity of
`⊗_p V_p^{λ^{(p)}}` in the coordinate ring of the quiver is the number of integer points of the
polytope of `positionalOf a b c` with weight `w`. -/
theorem multiplicity_eq_card_intPoints (w : ℕ → ℕ → ℤ) (lam : (canonicalQuiver a b c).Weight)
    (hlam : (canonicalQuiver a b c).IsDominant lam)
    (hw : ∀ p (l : Fin ((canonicalQuiver a b c).dim p)),
      w ((canonicalPart a b c).first p) l = lam p l) :
    (canonicalQuiver a b c).multiplicity lam =
      Nat.card ((positionalOf a b c).withWeight w).polytope.intPoints := by
  rw [(canonicalQuiver a b c).multiplicity_eq_card hlam,
    Nat.card_congr (intPointsEquiv a b c w lam hw)]

/-- **The lattice-point identity** `[𝒜_c](κ_a κ_b) = #(P(a, b, c) ∩ ℤ^M)` for every quiver
triple (Theorem 1.4). -/
theorem atomCoefficient_eq_card_intPoints
    (h : IsQuiverTriple (listComp c.length a) (listComp c.length b) (listComp c.length c)) :
    atomCoefficient (key (listComp c.length a) * key (listComp c.length b))
        (listComp c.length c) = Nat.card (quiverPolytope a b c).intPoints := by
  have hI := isQuiverTriple_iff_canonical.mp h
  rw [atomCoefficient_eq_multiplicity hI]
  exact multiplicity_eq_card_intPoints a b c _ _ (isDominant_leviWeight hI)
    (weight_positionalOf_first a b c)

/-- For a quiver triple, the polytope `P(a, b, c)` has finitely many integer points. -/
theorem finite_intPoints
    (h : IsQuiverTriple (listComp c.length a) (listComp c.length b) (listComp c.length c)) :
    (quiverPolytope a b c).intPoints.Finite :=
  finite_intPoints_withWeight a b c _ _ (isDominant_leviWeight (isQuiverTriple_iff_canonical.mp h))
    (weight_positionalOf_first a b c)

end Schubert.RS.Quiver.Flat
