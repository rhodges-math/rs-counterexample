import RSCounterexample.Paper.Quiver.Polytope.Decode
import RSCounterexample.Paper.Quiver.Polytope.Lattice
import RSCounterexample.Paper.Quiver.Extraction
import RSCounterexample.Paper.Quiver.Decomposition
import RSCounterexample.Paper.Statements.QuiverSaturation

/-!
# Positivity and nonemptiness

The second part of Theorem 1.4: for a quiver triple, the atom coefficient is positive iff the
polytope `P(a, b, c)` is nonempty, given the saturation statement `QuiverSaturation` as a
hypothesis.

* A multiplicity is positive iff some LR chains exist (`ForwardQuiver.multiplicity_pos_iff`).
* Saturation passes positivity from `N λ` to `λ` (`ForwardQuiver.multiplicity_pos_of_nsmul`).
* A real point of the positional polytope gives an integer point of the polytope of the weight
  `N λ` for some `N ≥ 1` (`PositionalQuiver.exists_intPoint_nsmul`): Fourier–Motzkin gives a
  rational point, and clearing denominators scales the right-hand sides, which are linear in the
  weight (`PositionalQuiver.polytope_withWeight_nsmul`).
* The integer points of the polytope of the weight `N λ` count the multiplicity of `N λ`
  (`Schubert.RS.Quiver.Flat.multiplicity_eq_card_intPoints`).

## Main results

* `Schubert.RS.Quiver.Flat.nonempty_of_quiverCoefficient_pos`: a positive coefficient gives a
  point of `P(a, b, c)`, real and rational (no hypothesis).
* `Schubert.RS.Quiver.Flat.quiverCoefficient_pos_iff_nonempty`: positivity iff `P(a, b, c) ≠ ∅`
  in `ℝ^M`.
* `Schubert.RS.Quiver.Flat.quiverCoefficient_pos_iff_ratFeasible`: the same with a rational point.
-/

namespace Schubert.RS.Quiver

namespace ForwardQuiver

variable (Q : ForwardQuiver) {lam : Q.Weight}

/-- **A multiplicity is positive iff LR chains exist.** -/
theorem multiplicity_pos_iff (hlam : Q.IsDominant lam) :
    0 < Q.multiplicity lam ↔ Nonempty (Σ μ : Q.ArrowShapes, Q.VertexChains μ lam) := by
  have := Q.finite_chains hlam
  rw [Q.multiplicity_eq_card hlam, Nat.cast_pos, Nat.card_pos_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, inferInstance⟩⟩

/-- **Saturation**: positivity of the multiplicity of `N λ`, for some `N ≥ 1`, implies positivity
for `λ`. -/
theorem multiplicity_pos_of_nsmul (hsat : QuiverSaturation) (hlam : Q.IsDominant lam) {N : ℕ}
    (hN : 0 < N) (h : 0 < Q.multiplicity (N • lam)) : 0 < Q.multiplicity lam :=
  hsat Q lam hlam N hN h

end ForwardQuiver

/-- The atom coefficient of a quiver triple is nonnegative. -/
theorem atomCoefficient_nonneg {n : ℕ} {a b c : Composition n} (h : IsQuiverTriple a b c) :
    0 ≤ atomCoefficient (key a * key b) c := by
  obtain ⟨I, hI⟩ := h
  rw [atomCoefficient_eq_multiplicity hI]
  exact (quiverOf a b c _ I).multiplicity_nonneg (isDominant_leviWeight hI)

namespace Flat

/-- An integer point is a point over every ordered field. -/
theorem points_nonempty_of_intPoints {P : IntPolyhedron} (h : P.intPoints.Nonempty)
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] : (P.points K).Nonempty := by
  obtain ⟨z, hz⟩ := h
  exact ⟨_, (IntPolyhedron.mem_intPoints_iff_cast z).1 hz⟩

namespace PositionalQuiver

variable (Q : PositionalQuiver)

/-- **A real point gives an integer point of a dilate**: if the polytope has a real point, then for
some `N ≥ 1` the polytope of the weight `N λ` has an integer point. -/
theorem exists_intPoint_nsmul (h : (Q.polytope.points ℝ).Nonempty) :
    ∃ N : ℕ, 0 < N ∧ ((Q.withWeight fun i l => N * Q.weight i l).polytope.intPoints).Nonempty := by
  obtain ⟨N, hN, hz⟩ :=
    IntPolyhedron.exists_intPoint_scaleRhs (IntPolyhedron.points_real_nonempty_iff_rat.1 h)
  exact ⟨N, hN, by rw [polytope_withWeight_nsmul]; exact hz⟩

end PositionalQuiver

/-! ### Theorem 1.4: positivity and nonemptiness -/

variable {a b c : List ℕ}

/-- **A positive coefficient gives a point of `P(a, b, c)`**: for a quiver triple with
`[𝒜_c](κ_a κ_b) > 0`, the polytope has an integer point, hence a real and a rational point. -/
theorem nonempty_of_quiverCoefficient_pos
    (h : IsQuiverTriple (listComp c.length a) (listComp c.length b) (listComp c.length c))
    (hpos : 0 < atomCoefficient (key (listComp c.length a) * key (listComp c.length b))
      (listComp c.length c)) :
    ((quiverPolytope a b c).points ℝ).Nonempty ∧ (quiverPolytope a b c).RatFeasible := by
  rw [atomCoefficient_eq_card_intPoints a b c h, Nat.cast_pos, Nat.card_pos_iff] at hpos
  obtain ⟨⟨z, hz⟩⟩ := hpos.1
  have hne : (quiverPolytope a b c).intPoints.Nonempty := ⟨z, hz⟩
  exact ⟨points_nonempty_of_intPoints hne ℝ,
    IntPolyhedron.ratFeasible_iff.2 (points_nonempty_of_intPoints hne ℚ)⟩

/-- **Theorem 1.4, positivity** (`P ⊆ ℝ^M`), given `QuiverSaturation` as a hypothesis: for a
quiver triple, `[𝒜_c](κ_a κ_b) > 0` iff the polytope `P(a, b, c)` is nonempty. -/
theorem quiverCoefficient_pos_iff_nonempty (hsat : QuiverSaturation)
    (h : IsQuiverTriple (listComp c.length a) (listComp c.length b) (listComp c.length c)) :
    0 < atomCoefficient (key (listComp c.length a) * key (listComp c.length b))
        (listComp c.length c) ↔ ((quiverPolytope a b c).points ℝ).Nonempty := by
  have hI := isQuiverTriple_iff_canonical.mp h
  have hdom : (canonicalQuiver a b c).IsDominant (canonicalWeight a b c) :=
    isDominant_leviWeight hI
  refine ⟨fun hpos => (nonempty_of_quiverCoefficient_pos h hpos).1, fun hx => ?_⟩
  obtain ⟨N, hN, hz⟩ := (positionalOf a b c).exists_intPoint_nsmul hx
  have hw : ∀ p (l : Fin ((canonicalQuiver a b c).dim p)),
      (fun i l => (N : ℤ) * (positionalOf a b c).weight i l) ((canonicalPart a b c).first p) l =
        (N • canonicalWeight a b c) p l := by
    intro p l
    simp only [weight_positionalOf_first, Pi.smul_apply, nsmul_eq_mul]
  have hfin := finite_intPoints_withWeight a b c
    (fun i l => (N : ℤ) * (positionalOf a b c).weight i l) _ (hdom.smul N) hw
  have hposN : 0 < (canonicalQuiver a b c).multiplicity (N • canonicalWeight a b c) := by
    rw [multiplicity_eq_card_intPoints a b c
      (fun i l => (N : ℤ) * (positionalOf a b c).weight i l) _ (hdom.smul N) hw, Nat.cast_pos,
      Nat.card_pos_iff]
    exact ⟨hz.to_subtype, hfin.to_subtype⟩
  rw [atomCoefficient_eq_multiplicity hI]
  exact (canonicalQuiver a b c).multiplicity_pos_of_nsmul hsat hdom hN hposN

/-- **Theorem 1.4, positivity, rational form**, given `QuiverSaturation` as a hypothesis: for a
quiver triple, `[𝒜_c](κ_a κ_b) > 0` iff the system `P(a, b, c)` has a rational solution. -/
theorem quiverCoefficient_pos_iff_ratFeasible (hsat : QuiverSaturation)
    (h : IsQuiverTriple (listComp c.length a) (listComp c.length b) (listComp c.length c)) :
    0 < atomCoefficient (key (listComp c.length a) * key (listComp c.length b))
        (listComp c.length c) ↔ (quiverPolytope a b c).RatFeasible :=
  (quiverCoefficient_pos_iff_nonempty hsat h).trans
    (IntPolyhedron.points_real_nonempty_iff_rat.trans IntPolyhedron.ratFeasible_iff.symm)

end Flat

end Schubert.RS.Quiver
