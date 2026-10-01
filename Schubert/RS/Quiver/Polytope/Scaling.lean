import Schubert.RS.Quiver.Polytope.Positivity

/-!
# Nonemptiness of `P(a, b, c)` without saturation

For a quiver triple `(a, b, c)` and `N ≥ 1`, the dilated triple `(N a, N b, N c)` is again a
quiver triple, with the same canonical partition and the same quiver, and with the weight `N λ`
(`isQuiverPartition_nsmul`, `canonicalPartition_nsmul`, `quiverOf_nsmul`, `leviWeight_nsmul`).
Its atom coefficient counts the integer points of the dilate `N · P(a, b, c)`, the system with
right-hand sides multiplied by `N` (`Flat.atomCoefficient_nsmul_eq_card`). Since a system with
integer data has a real point iff some dilate has an integer point
(`IntPolyhedron.points_nonempty_iff_exists_scaleRhs`), this gives, with no hypothesis,

  `P(a, b, c) ≠ ∅  ⇔  [𝒜_{N c}](κ_{N a} κ_{N b}) > 0 for some N ≥ 1`

(`Flat.quiverPolytope_nonempty_iff_exists_nsmul_pos`, and the rational form
`Flat.quiverPolytope_ratFeasible_iff_exists_nsmul_pos`). This is the part of the equivalence
`[𝒜_c](κ_a κ_b) > 0 ⇔ P(a, b, c) ≠ ∅` of Theorem 1.4 that does not use saturation.

## Main results

* `Schubert.RS.IntPolyhedron.points_nonempty_iff_exists_scaleRhs`
* `Schubert.RS.Quiver.isQuiverTriple_nsmul`, `Schubert.RS.Quiver.canonicalPartition_nsmul`,
  `Schubert.RS.Quiver.atomCoefficient_nsmul`
* `Schubert.RS.Quiver.Flat.atomCoefficient_nsmul_eq_card`
* `Schubert.RS.Quiver.Flat.quiverPolytope_nonempty_iff_exists_nsmul_pos`,
  `Schubert.RS.Quiver.Flat.quiverPolytope_ratFeasible_iff_exists_nsmul_pos`
-/

namespace Schubert.RS

/-! ### Dilates of a system of inequalities -/

namespace IntPolyhedron

variable (P : IntPolyhedron) {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- An integer point `z` of the dilate `a · x ≤ N β` gives the point `z / N` of `a · x ≤ β`. -/
theorem div_mem_points_of_mem_intPoints_scaleRhs {N : ℕ} (hN : 0 < N)
    {z : Fin P.dim → ℤ} (hz : z ∈ (P.scaleRhs N).intPoints) :
    (fun i => (z i : K) / N) ∈ P.points K := by
  intro r hr
  have h := hz (r.1, (N : ℤ) * r.2) (List.mem_map_of_mem hr)
  have hNK : (0 : K) < N := by exact_mod_cast hN
  have hcast : ∑ i : Fin P.dim, (r.1.getD i 0 : K) * (z i : K) ≤ (N : K) * r.2 := by
    exact_mod_cast h
  simp only [rowValue]
  calc ∑ i : Fin P.dim, (r.1.getD i 0 : K) * ((z i : K) / N)
      = (∑ i : Fin P.dim, (r.1.getD i 0 : K) * (z i : K)) / N := by
        rw [div_eq_mul_inv, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by rw [div_eq_mul_inv]; ring
    _ ≤ (N : K) * r.2 / N := div_le_div_of_nonneg_right hcast hNK.le
    _ = r.2 := mul_div_cancel_left₀ _ hNK.ne'

/-- **A system with integer data has a point iff some dilate has an integer point**: over every
linearly ordered field, `a · x ≤ β` is solvable iff `a · x ≤ N β` has an integer solution for
some `N ≥ 1`. -/
theorem points_nonempty_iff_exists_scaleRhs :
    (P.points K).Nonempty ↔ ∃ N ≥ 1, (P.scaleRhs N).intPoints.Nonempty := by
  constructor
  · intro h
    obtain ⟨N, hN, hz⟩ := exists_intPoint_scaleRhs ((points_nonempty_congr ℚ).1 h)
    exact ⟨N, hN, hz⟩
  · rintro ⟨N, hN, z, hz⟩
    exact ⟨_, P.div_mem_points_of_mem_intPoints_scaleRhs hN hz⟩

end IntPolyhedron

/-! ### Dilating a quiver triple -/

namespace Quiver

variable {n : ℕ} {a b c : Composition n} {M N : ℕ} {I : IntervalPartition n}

theorem cmp_nsmul (hN : 0 < N) (P Q : ℕ × ℕ × ℕ) :
    Window.cmp (N * P.1, N * P.2.1, N * P.2.2) (N * Q.1, N * Q.2.1, N * Q.2.2) =
      Window.cmp P Q := by
  simp only [Window.cmp, Nat.mul_lt_mul_left hN]

theorem complement_nsmul (N M : ℕ) (c : Composition n) :
    Window.complement (N * M) (N • c) = N • Window.complement M c := by
  funext i
  simp only [Window.complement, Pi.smul_apply, smul_eq_mul, Nat.mul_sub]

theorem cmp_triple_nsmul (hN : 0 < N) (a b g : Composition n) (i j : Fin n) :
    Window.cmp (Window.triple (N • a) (N • b) (N • g) i)
        (Window.triple (N • a) (N • b) (N • g) j) =
      Window.cmp (Window.triple a b g i) (Window.triple a b g j) := by
  simp only [Window.triple, Pi.smul_apply, smul_eq_mul]
  exact cmp_nsmul hN (a i, b i, g i) (a j, b j, g j)

theorem residual_nsmul (N : ℕ) (a b c : Composition n) :
    Window.residual (N • a) (N • b) (N • c) = N • Window.residual a b c := by
  funext i
  simp only [Window.residual, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

theorem prefixHeight_nsmul (N : ℕ) (a b c : Composition n) :
    Window.prefixHeight (N • a) (N • b) (N • c) =
      fun k => (N : ℤ) * Window.prefixHeight a b c k := by
  funext k
  unfold Window.prefixHeight
  rw [residual_nsmul, Finset.mul_sum]
  simp only [Pi.smul_apply, nsmul_eq_mul]

theorem windowInequality_nsmul (hN : 0 < N) {u : Composition n} {h : ℕ → ℤ}
    (hw : Window.WindowInequality u h) :
    Window.WindowInequality (N • u) fun k => (N : ℤ) * h k := by
  intro i j hij hlt
  simp only [Pi.smul_apply, smul_eq_mul, Nat.mul_lt_mul_left hN] at hlt
  obtain ⟨k, hk1, hk2, hk3⟩ := hw i j hij hlt
  refine ⟨k, hk1, hk2, ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  have h1 : h (k + 1) ≤ (u j : ℤ) - u i := by omega
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℤ) ≤ N)
  linarith

/-- The hypotheses of Proposition 2.13 are preserved by dilation. -/
theorem hypotheses_nsmul (hN : 0 < N) (h : Window.Hypotheses a b c M) :
    Window.Hypotheses (N • a) (N • b) (N • c) (N * M) where
  balance := by
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, ← mul_add, h.balance]
  le_N i := by
    simp only [Pi.smul_apply, smul_eq_mul]
    exact Nat.mul_le_mul_left N (h.le_N i)
  height_nonneg k := by
    rw [prefixHeight_nsmul]
    exact mul_nonneg (by positivity) (h.height_nonneg k)
  window_a := by
    rw [prefixHeight_nsmul]
    exact windowInequality_nsmul hN h.window_a
  window_b := by
    rw [prefixHeight_nsmul]
    exact windowInequality_nsmul hN h.window_b
  window_c := by
    rw [prefixHeight_nsmul, complement_nsmul]
    exact windowInequality_nsmul hN h.window_c

/-- **Dilating a quiver partition**: for `N ≥ 1`, `I` is a quiver partition of `(N a, N b, N c)`
(with the bound `N M`). -/
theorem isQuiverPartition_nsmul (hN : 0 < N) (h : IsQuiverPartition a b c M I) :
    IsQuiverPartition (N • a) (N • b) (N • c) (N * M) I where
  hyp := hypotheses_nsmul hN h.hyp
  antitone i j hij hI := by
    obtain ⟨h1, h2, h3⟩ := h.antitone i j hij hI
    rw [complement_nsmul]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact ⟨Nat.mul_le_mul_left N h1, Nat.mul_le_mul_left N h2, Nat.mul_le_mul_left N h3⟩
  cmp_const p q hpq := by
    obtain ⟨k, hk⟩ := h.cmp_const p q hpq
    refine ⟨k, fun i j hi hj => ?_⟩
    rw [complement_nsmul, cmp_triple_nsmul hN]
    exact hk i j hi hj

/-- **Dilating a quiver triple** gives a quiver triple. -/
theorem isQuiverTriple_nsmul (hN : 0 < N) (h : IsQuiverTriple a b c) :
    IsQuiverTriple (N • a) (N • b) (N • c) := by
  obtain ⟨I, hI⟩ := h
  refine (isQuiverTriple_iff_of_le (N := N * Finset.univ.sup c) fun i => ?_).2
    ⟨I, isQuiverPartition_nsmul hN hI⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  exact Nat.mul_le_mul_left N (le_sup c i)

/-- A quiver triple and its dilates have the same canonical partition. -/
theorem canonicalPartition_nsmul (hN : 0 < N) (h : IsQuiverTriple a b c) :
    canonicalPartition (N • a) (N • b) (N • c) = canonicalPartition a b c :=
  (isQuiverPartition_nsmul hN (isQuiverTriple_iff_canonical.mp h)).eq_canonical.symm

/-- A quiver partition and its dilates have the same quiver. -/
theorem quiverOf_nsmul (hN : 0 < N) :
    quiverOf (N • a) (N • b) (N • c) (N * M) I = quiverOf a b c M I := by
  unfold quiverOf
  congr 1
  funext p q
  rw [complement_nsmul, cmp_triple_nsmul hN]

/-- Dilating the triple dilates the weight. -/
theorem leviWeight_nsmul (N : ℕ) :
    leviWeight (N • a) (N • b) (N • c) I = N • leviWeight a b c I := by
  funext p k
  simp only [leviWeight, residual_nsmul, Pi.smul_apply]

/-- **The atom coefficient of a dilated quiver triple** is the multiplicity of the dilated weight in
the same quiver. -/
theorem atomCoefficient_nsmul (hN : 0 < N) (h : IsQuiverPartition a b c M I) :
    atomCoefficient (key (N • a) * key (N • b)) (N • c) =
      (quiverOf a b c M I).multiplicity (N • leviWeight a b c I) := by
  rw [atomCoefficient_eq_multiplicity (isQuiverPartition_nsmul hN h), leviWeight_nsmul]
  congr 1
  exact quiverOf_nsmul hN

/-! ### The polytope and the dilated coefficients -/

namespace Flat

variable {a b c : List ℕ}

theorem weight_nsmul_agrees (N : ℕ) :
    ∀ p (l : Fin ((canonicalQuiver a b c).dim p)),
      (fun i l => (N : ℤ) * (positionalOf a b c).weight i l) ((canonicalPart a b c).first p) l =
        (N • canonicalWeight a b c) p l := by
  intro p l
  simp only [weight_positionalOf_first, Pi.smul_apply, nsmul_eq_mul]

/-- The dilates of `P(a, b, c)` have finitely many integer points. -/
theorem finite_intPoints_scaleRhs
    (h : IsQuiverTriple (listComp c.length a) (listComp c.length b) (listComp c.length c))
    (N : ℕ) : ((quiverPolytope a b c).scaleRhs N).intPoints.Finite := by
  have hdom : (canonicalQuiver a b c).IsDominant (canonicalWeight a b c) :=
    isDominant_leviWeight (isQuiverTriple_iff_canonical.mp h)
  have := finite_intPoints_withWeight a b c
    (fun i l => (N : ℤ) * (positionalOf a b c).weight i l) _ (hdom.smul N) (weight_nsmul_agrees N)
  rwa [PositionalQuiver.polytope_withWeight_nsmul] at this

/-- **The dilates count the dilated coefficients**: for a quiver triple and `N ≥ 1`,
`[𝒜_{N c}](κ_{N a} κ_{N b}) = #(N · P(a, b, c) ∩ ℤ^M)`, where `N · P(a, b, c)` is the system with
right-hand sides multiplied by `N`. -/
theorem atomCoefficient_nsmul_eq_card
    (h : IsQuiverTriple (listComp c.length a) (listComp c.length b) (listComp c.length c))
    {N : ℕ} (hN : 0 < N) :
    atomCoefficient (key (N • listComp c.length a) * key (N • listComp c.length b))
        (N • listComp c.length c) = Nat.card ((quiverPolytope a b c).scaleRhs N).intPoints := by
  have hI := isQuiverTriple_iff_canonical.mp h
  have hdom : (canonicalQuiver a b c).IsDominant (canonicalWeight a b c) :=
    isDominant_leviWeight hI
  rw [atomCoefficient_nsmul hN hI, multiplicity_eq_card_intPoints a b c
    (fun i l => (N : ℤ) * (positionalOf a b c).weight i l) _ (hdom.smul N)
    (weight_nsmul_agrees N), PositionalQuiver.polytope_withWeight_nsmul]
  rfl

/-- For `N ≥ 1`, the dilated coefficient is positive iff the dilate has an integer point. -/
theorem atomCoefficient_nsmul_pos_iff
    (h : IsQuiverTriple (listComp c.length a) (listComp c.length b) (listComp c.length c))
    {N : ℕ} (hN : 0 < N) :
    0 < atomCoefficient (key (N • listComp c.length a) * key (N • listComp c.length b))
        (N • listComp c.length c) ↔ ((quiverPolytope a b c).scaleRhs N).intPoints.Nonempty := by
  rw [atomCoefficient_nsmul_eq_card h hN, Nat.cast_pos, Nat.card_pos_iff]
  have hfin := finite_intPoints_scaleRhs h N
  exact ⟨fun h' => Set.nonempty_coe_sort.mp h'.1, fun h' => ⟨h'.to_subtype, hfin.to_subtype⟩⟩

/-- **Theorem 1.4, nonemptiness without saturation**: for a quiver triple, the polytope
`P(a, b, c) ⊆ ℝ^M` is nonempty iff `[𝒜_{N c}](κ_{N a} κ_{N b}) > 0` for some `N ≥ 1`. -/
theorem quiverPolytope_nonempty_iff_exists_nsmul_pos
    (h : IsQuiverTriple (listComp c.length a) (listComp c.length b) (listComp c.length c)) :
    ((quiverPolytope a b c).points ℝ).Nonempty ↔
      ∃ N ≥ 1, 0 < atomCoefficient (key (N • listComp c.length a) * key (N • listComp c.length b))
        (N • listComp c.length c) := by
  rw [IntPolyhedron.points_nonempty_iff_exists_scaleRhs]
  exact exists_congr fun N => and_congr_right fun hN => (atomCoefficient_nsmul_pos_iff h hN).symm

/-- **Theorem 1.4, nonemptiness without saturation, rational form**: for a quiver triple, the
system `P(a, b, c)` has a rational solution iff `[𝒜_{N c}](κ_{N a} κ_{N b}) > 0` for some
`N ≥ 1`. -/
theorem quiverPolytope_ratFeasible_iff_exists_nsmul_pos
    (h : IsQuiverTriple (listComp c.length a) (listComp c.length b) (listComp c.length c)) :
    (quiverPolytope a b c).RatFeasible ↔
      ∃ N ≥ 1, 0 < atomCoefficient (key (N • listComp c.length a) * key (N • listComp c.length b))
        (N • listComp c.length c) :=
  IntPolyhedron.ratFeasible_iff.trans ((IntPolyhedron.points_nonempty_congr ℝ).trans
    (quiverPolytope_nonempty_iff_exists_nsmul_pos h))

end Flat

end Quiver

end Schubert.RS
