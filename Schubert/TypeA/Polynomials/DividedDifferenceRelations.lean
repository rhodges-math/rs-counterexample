import Schubert.TypeA.Polynomials.DividedDifferences
import Mathlib.GroupTheory.Perm.Sign

/-!
# Nil-Coxeter relations for divided differences

This file develops the adjacent braid relation from the integral
alternating-quotient identity.  No localization is used: a Vandermonde
product is introduced and then cancelled in the polynomial domain.
-/

namespace Schubert

namespace Schubert

noncomputable section

open FinPermutation

variable {n : ℕ}

/-- The simple root `x_i-x_(i+1)`. -/
def adjacentRootPolynomial (a : AdjacentPosition n) :
    BorelPresentation.PolynomialRing n :=
  MvPolynomial.X a.left - MvPolynomial.X a.right

/-- For consecutive adjacent positions, the intervening long root
`x_i-x_(i+2)`. -/
def consecutiveLongRoot (a b : AdjacentPosition n) :
    BorelPresentation.PolynomialRing n :=
  MvPolynomial.X a.left - MvPolynomial.X b.right

theorem adjacentRootPolynomial_ne_zero (a : AdjacentPosition n) :
    adjacentRootPolynomial a ≠ 0 :=
  adjacentRoot_ne_zero a

theorem adjacentTransposition_braid
    (a b : AdjacentPosition n) (hab : a.right = b.left) :
    (adjacentTransposition a : Fin n → Fin n) ∘
        adjacentTransposition b ∘ adjacentTransposition a =
      (adjacentTransposition b : Fin n → Fin n) ∘
        adjacentTransposition a ∘ adjacentTransposition b := by
  have hxy : a.left ≠ b.left := by
    rw [← hab]
    exact a.left_ne_right
  have hyz : b.left ≠ b.right := b.left_ne_right
  have hxz : a.left ≠ b.right :=
    (a.left_lt_right.trans (hab ▸ b.left_lt_right)).ne
  have hgroup : Equiv.swap a.left b.left * Equiv.swap b.left b.right *
      Equiv.swap a.left b.left =
      Equiv.swap b.left b.right * Equiv.swap a.left b.left *
        Equiv.swap b.left b.right := by
    calc
      Equiv.swap a.left b.left * Equiv.swap b.left b.right *
          Equiv.swap a.left b.left = Equiv.swap a.left b.right := by
        rw [Equiv.swap_comm a.left b.left,
          Equiv.swap_comm b.left b.right]
        exact Equiv.swap_mul_swap_mul_swap hyz.symm hxz.symm
      _ = Equiv.swap b.right a.left := Equiv.swap_comm _ _
      _ = Equiv.swap b.left b.right * Equiv.swap a.left b.left *
          Equiv.swap b.left b.right :=
        (Equiv.swap_mul_swap_mul_swap hxy hxz).symm
  funext k
  have hk := DFunLike.congr_fun hgroup k
  simpa only [Function.comp_apply, Equiv.Perm.mul_apply,
    adjacentTransposition, hab] using hk

/-- Adjacent variable swaps satisfy the type-A braid relation. -/
theorem adjacentVariableSwap_braid
    (a b : AdjacentPosition n) (hab : a.right = b.left)
    (p : BorelPresentation.PolynomialRing n) :
    adjacentVariableSwap a
        (adjacentVariableSwap b (adjacentVariableSwap a p)) =
      adjacentVariableSwap b
        (adjacentVariableSwap a (adjacentVariableSwap b p)) := by
  simp only [adjacentVariableSwap, MvPolynomial.renameEquiv_apply]
  simp_rw [MvPolynomial.rename_rename]
  congr 2
  exact adjacentTransposition_braid a b hab

private theorem consecutive_endpoint_ne
    (a b : AdjacentPosition n) (hab : a.right = b.left) :
    a.left ≠ b.right :=
  (a.left_lt_right.trans (hab ▸ b.left_lt_right)).ne

private theorem b_right_ne_a_right
    (a b : AdjacentPosition n) (hab : a.right = b.left) :
    b.right ≠ a.right := by
  rw [hab]
  exact b.left_ne_right.symm

private theorem a_left_ne_b_left
    (a b : AdjacentPosition n) (hab : a.right = b.left) :
    a.left ≠ b.left := by
  rw [← hab]
  exact a.left_ne_right

theorem swap_a_root_a
    (a : AdjacentPosition n) :
  adjacentVariableSwap a (adjacentRootPolynomial a) =
      -adjacentRootPolynomial a := by
  simp [adjacentRootPolynomial]

theorem swap_b_root_b
    (b : AdjacentPosition n) :
    adjacentVariableSwap b (adjacentRootPolynomial b) =
      -adjacentRootPolynomial b :=
  swap_a_root_a b

theorem swap_a_root_b
    (a b : AdjacentPosition n) (hab : a.right = b.left) :
    adjacentVariableSwap a (adjacentRootPolynomial b) =
      consecutiveLongRoot a b := by
  rw [adjacentRootPolynomial, consecutiveLongRoot, map_sub, ← hab,
    adjacentVariableSwap_X_right]
  rw [adjacentVariableSwap_X_other a b.right
    (consecutive_endpoint_ne a b hab).symm
    (b_right_ne_a_right a b hab)]

theorem swap_a_longRoot
    (a b : AdjacentPosition n) (hab : a.right = b.left) :
    adjacentVariableSwap a (consecutiveLongRoot a b) =
      adjacentRootPolynomial b := by
  rw [consecutiveLongRoot, adjacentRootPolynomial, map_sub,
    adjacentVariableSwap_X_left]
  rw [adjacentVariableSwap_X_other a b.right
    (consecutive_endpoint_ne a b hab).symm
    (b_right_ne_a_right a b hab), hab]

theorem swap_b_root_a
    (a b : AdjacentPosition n) (hab : a.right = b.left) :
    adjacentVariableSwap b (adjacentRootPolynomial a) =
      consecutiveLongRoot a b := by
  rw [adjacentRootPolynomial, consecutiveLongRoot, map_sub, hab,
    adjacentVariableSwap_X_left]
  rw [adjacentVariableSwap_X_other b a.left
    (a_left_ne_b_left a b hab) (consecutive_endpoint_ne a b hab)]

theorem swap_b_longRoot
    (a b : AdjacentPosition n) (hab : a.right = b.left) :
    adjacentVariableSwap b (consecutiveLongRoot a b) =
      adjacentRootPolynomial a := by
  rw [consecutiveLongRoot, adjacentRootPolynomial, map_sub,
    adjacentVariableSwap_X_right, ← hab]
  rw [adjacentVariableSwap_X_other b a.left
    (a_left_ne_b_left a b hab) (consecutive_endpoint_ne a b hab)]

theorem adjacentRoot_add_eq_longRoot
    (a b : AdjacentPosition n) (hab : a.right = b.left) :
    adjacentRootPolynomial a + adjacentRootPolynomial b =
      consecutiveLongRoot a b := by
  simp [adjacentRootPolynomial, consecutiveLongRoot, hab]

theorem swap_a_root_b_mul_longRoot
    (a b : AdjacentPosition n) (hab : a.right = b.left) :
    adjacentVariableSwap a
        (adjacentRootPolynomial b * consecutiveLongRoot a b) =
      adjacentRootPolynomial b * consecutiveLongRoot a b := by
  rw [map_mul, swap_a_root_b a b hab, swap_a_longRoot a b hab]
  ring

theorem swap_b_root_a_mul_longRoot
    (a b : AdjacentPosition n) (hab : a.right = b.left) :
    adjacentVariableSwap b
        (adjacentRootPolynomial a * consecutiveLongRoot a b) =
      adjacentRootPolynomial a * consecutiveLongRoot a b := by
  rw [map_mul, swap_b_root_a a b hab, swap_b_longRoot a b hab]
  ring

private theorem consecutiveLongRoot_ne_zero
    (a b : AdjacentPosition n) (hab : a.right = b.left) :
    consecutiveLongRoot a b ≠ 0 := by
  rw [consecutiveLongRoot, sub_ne_zero]
  exact fun h => (consecutive_endpoint_ne a b hab)
    (MvPolynomial.X_injective h)

/-- The three positive roots occurring in an adjacent braid have nonzero
product.  This is the factor cancelled in the integral proof below. -/
theorem adjacentVandermonde_ne_zero
    (a b : AdjacentPosition n) (hab : a.right = b.left) :
    adjacentRootPolynomial a * consecutiveLongRoot a b *
        adjacentRootPolynomial b ≠ 0 :=
  mul_ne_zero
    (mul_ne_zero (adjacentRootPolynomial_ne_zero a)
      (consecutiveLongRoot_ne_zero a b hab))
    (adjacentRootPolynomial_ne_zero b)

private theorem left_braid_scaled
    (a b : AdjacentPosition n) (hab : a.right = b.left)
    (p : BorelPresentation.PolynomialRing n) :
    (adjacentRootPolynomial a * consecutiveLongRoot a b *
        adjacentRootPolynomial b) *
        adjacentDividedDifference a
          (adjacentDividedDifference b (adjacentDividedDifference a p)) =
      p - adjacentVariableSwap a p - adjacentVariableSwap b p +
        adjacentVariableSwap b (adjacentVariableSwap a p) +
        adjacentVariableSwap a (adjacentVariableSwap b p) -
        adjacentVariableSwap a
          (adjacentVariableSwap b (adjacentVariableSwap a p)) := by
  have hrootA (q : BorelPresentation.PolynomialRing n) :
      adjacentRootPolynomial a * adjacentDividedDifference a q =
        q - adjacentVariableSwap a q := by
    exact adjacentRoot_mul_adjacentDividedDifference a q
  have hrootB (q : BorelPresentation.PolynomialRing n) :
      adjacentRootPolynomial b * adjacentDividedDifference b q =
        q - adjacentVariableSwap b q := by
    exact adjacentRoot_mul_adjacentDividedDifference b q
  have hfirstSwap :
      adjacentVariableSwap a
          (consecutiveLongRoot a b *
            (adjacentRootPolynomial b *
              adjacentDividedDifference b (adjacentDividedDifference a p))) =
        consecutiveLongRoot a b *
          (adjacentRootPolynomial b *
            adjacentVariableSwap a
              (adjacentDividedDifference b (adjacentDividedDifference a p))) := by
    simp only [map_mul, swap_a_longRoot a b hab,
      swap_a_root_b a b hab]
    ring
  have hlongTimesSwap :
      consecutiveLongRoot a b *
          adjacentVariableSwap b (adjacentDividedDifference a p) =
        adjacentVariableSwap b
          (adjacentRootPolynomial a * adjacentDividedDifference a p) := by
    rw [map_mul, swap_b_root_a a b hab]
  have hmiddle :
      consecutiveLongRoot a b *
          (adjacentDividedDifference a p -
            adjacentVariableSwap b (adjacentDividedDifference a p)) =
        (p - adjacentVariableSwap a p) +
          adjacentRootPolynomial b * adjacentDividedDifference a p -
          adjacentVariableSwap b p +
          adjacentVariableSwap b (adjacentVariableSwap a p) := by
    calc
      consecutiveLongRoot a b *
          (adjacentDividedDifference a p -
            adjacentVariableSwap b (adjacentDividedDifference a p)) =
        (adjacentRootPolynomial a + adjacentRootPolynomial b) *
            adjacentDividedDifference a p -
          consecutiveLongRoot a b *
            adjacentVariableSwap b (adjacentDividedDifference a p) := by
              rw [adjacentRoot_add_eq_longRoot a b hab]
              ring
      _ = adjacentRootPolynomial a * adjacentDividedDifference a p +
          adjacentRootPolynomial b * adjacentDividedDifference a p -
          adjacentVariableSwap b
            (adjacentRootPolynomial a * adjacentDividedDifference a p) := by
              rw [hlongTimesSwap]
              ring
      _ = (p - adjacentVariableSwap a p) +
          adjacentRootPolynomial b * adjacentDividedDifference a p -
          adjacentVariableSwap b
            (p - adjacentVariableSwap a p) := by
              rw [hrootA p]
      _ = (p - adjacentVariableSwap a p) +
          adjacentRootPolynomial b * adjacentDividedDifference a p -
          adjacentVariableSwap b p +
          adjacentVariableSwap b (adjacentVariableSwap a p) := by
              rw [map_sub]
              ring
  have hmiddleSwap :
      adjacentVariableSwap a
        (consecutiveLongRoot a b *
          (adjacentDividedDifference a p -
            adjacentVariableSwap b (adjacentDividedDifference a p))) =
        adjacentRootPolynomial b * adjacentDividedDifference a p -
          adjacentVariableSwap a (adjacentVariableSwap b p) +
          adjacentVariableSwap a
            (adjacentVariableSwap b (adjacentVariableSwap a p)) := by
    rw [hmiddle]
    simp only [map_add, map_sub, map_mul,
      adjacentVariableSwap_involutive,
      adjacentVariableSwap_adjacentDividedDifference,
      swap_a_root_b a b hab]
    rw [← adjacentRoot_add_eq_longRoot a b hab, add_mul, hrootA p]
    ring
  calc
    (adjacentRootPolynomial a * consecutiveLongRoot a b *
        adjacentRootPolynomial b) *
        adjacentDividedDifference a
          (adjacentDividedDifference b (adjacentDividedDifference a p)) =
      consecutiveLongRoot a b * adjacentRootPolynomial b *
        (adjacentRootPolynomial a *
          adjacentDividedDifference a
            (adjacentDividedDifference b
              (adjacentDividedDifference a p))) := by ring
    _ = consecutiveLongRoot a b * adjacentRootPolynomial b *
        (adjacentDividedDifference b (adjacentDividedDifference a p) -
          adjacentVariableSwap a
            (adjacentDividedDifference b (adjacentDividedDifference a p))) := by
      rw [hrootA]
    _ = consecutiveLongRoot a b *
          (adjacentRootPolynomial b *
            adjacentDividedDifference b (adjacentDividedDifference a p)) -
        adjacentVariableSwap a
          (consecutiveLongRoot a b *
            (adjacentRootPolynomial b *
              adjacentDividedDifference b (adjacentDividedDifference a p))) := by
      rw [hfirstSwap]
      ring
    _ = consecutiveLongRoot a b *
          (adjacentDividedDifference a p -
            adjacentVariableSwap b (adjacentDividedDifference a p)) -
        adjacentVariableSwap a
          (consecutiveLongRoot a b *
            (adjacentDividedDifference a p -
              adjacentVariableSwap b (adjacentDividedDifference a p))) := by
      rw [hrootB]
    _ = p - adjacentVariableSwap a p - adjacentVariableSwap b p +
        adjacentVariableSwap b (adjacentVariableSwap a p) +
        adjacentVariableSwap a (adjacentVariableSwap b p) -
        adjacentVariableSwap a
          (adjacentVariableSwap b (adjacentVariableSwap a p)) := by
      rw [hmiddleSwap, hmiddle]
      ring

private theorem right_braid_scaled
    (a b : AdjacentPosition n) (hab : a.right = b.left)
    (p : BorelPresentation.PolynomialRing n) :
    (adjacentRootPolynomial a * consecutiveLongRoot a b *
        adjacentRootPolynomial b) *
        adjacentDividedDifference b
          (adjacentDividedDifference a (adjacentDividedDifference b p)) =
      p - adjacentVariableSwap b p - adjacentVariableSwap a p +
        adjacentVariableSwap a (adjacentVariableSwap b p) +
        adjacentVariableSwap b (adjacentVariableSwap a p) -
        adjacentVariableSwap b
          (adjacentVariableSwap a (adjacentVariableSwap b p)) := by
  have hrootA (q : BorelPresentation.PolynomialRing n) :
      adjacentRootPolynomial a * adjacentDividedDifference a q =
        q - adjacentVariableSwap a q := by
    exact adjacentRoot_mul_adjacentDividedDifference a q
  have hrootB (q : BorelPresentation.PolynomialRing n) :
      adjacentRootPolynomial b * adjacentDividedDifference b q =
        q - adjacentVariableSwap b q := by
    exact adjacentRoot_mul_adjacentDividedDifference b q
  have hfirstSwap :
      adjacentVariableSwap b
          (consecutiveLongRoot a b *
            (adjacentRootPolynomial a *
              adjacentDividedDifference a (adjacentDividedDifference b p))) =
        consecutiveLongRoot a b *
          (adjacentRootPolynomial a *
            adjacentVariableSwap b
              (adjacentDividedDifference a (adjacentDividedDifference b p))) := by
    simp only [map_mul, swap_b_longRoot a b hab,
      swap_b_root_a a b hab]
    ring
  have hlongTimesSwap :
      consecutiveLongRoot a b *
          adjacentVariableSwap a (adjacentDividedDifference b p) =
        adjacentVariableSwap a
          (adjacentRootPolynomial b * adjacentDividedDifference b p) := by
    rw [map_mul, swap_a_root_b a b hab]
  have hmiddle :
      consecutiveLongRoot a b *
          (adjacentDividedDifference b p -
            adjacentVariableSwap a (adjacentDividedDifference b p)) =
        (p - adjacentVariableSwap b p) +
          adjacentRootPolynomial a * adjacentDividedDifference b p -
          adjacentVariableSwap a p +
          adjacentVariableSwap a (adjacentVariableSwap b p) := by
    calc
      consecutiveLongRoot a b *
          (adjacentDividedDifference b p -
            adjacentVariableSwap a (adjacentDividedDifference b p)) =
        (adjacentRootPolynomial a + adjacentRootPolynomial b) *
            adjacentDividedDifference b p -
          consecutiveLongRoot a b *
            adjacentVariableSwap a (adjacentDividedDifference b p) := by
              rw [adjacentRoot_add_eq_longRoot a b hab]
              ring
      _ = adjacentRootPolynomial a * adjacentDividedDifference b p +
          adjacentRootPolynomial b * adjacentDividedDifference b p -
          adjacentVariableSwap a
            (adjacentRootPolynomial b * adjacentDividedDifference b p) := by
              rw [hlongTimesSwap]
              ring
      _ = adjacentRootPolynomial a * adjacentDividedDifference b p +
          (p - adjacentVariableSwap b p) -
          adjacentVariableSwap a
            (p - adjacentVariableSwap b p) := by
              rw [hrootB p]
      _ = (p - adjacentVariableSwap b p) +
          adjacentRootPolynomial a * adjacentDividedDifference b p -
          adjacentVariableSwap a p +
          adjacentVariableSwap a (adjacentVariableSwap b p) := by
              rw [map_sub]
              ring
  have hmiddleSwap :
      adjacentVariableSwap b
        (consecutiveLongRoot a b *
          (adjacentDividedDifference b p -
            adjacentVariableSwap a (adjacentDividedDifference b p))) =
        adjacentRootPolynomial a * adjacentDividedDifference b p -
          adjacentVariableSwap b (adjacentVariableSwap a p) +
          adjacentVariableSwap b
            (adjacentVariableSwap a (adjacentVariableSwap b p)) := by
    rw [hmiddle]
    simp only [map_add, map_sub, map_mul,
      adjacentVariableSwap_involutive,
      adjacentVariableSwap_adjacentDividedDifference,
      swap_b_root_a a b hab]
    rw [← adjacentRoot_add_eq_longRoot a b hab, add_mul, hrootB p]
    ring
  calc
    (adjacentRootPolynomial a * consecutiveLongRoot a b *
        adjacentRootPolynomial b) *
        adjacentDividedDifference b
          (adjacentDividedDifference a (adjacentDividedDifference b p)) =
      consecutiveLongRoot a b * adjacentRootPolynomial a *
        (adjacentRootPolynomial b *
          adjacentDividedDifference b
            (adjacentDividedDifference a
              (adjacentDividedDifference b p))) := by ring
    _ = consecutiveLongRoot a b * adjacentRootPolynomial a *
        (adjacentDividedDifference a (adjacentDividedDifference b p) -
          adjacentVariableSwap b
            (adjacentDividedDifference a (adjacentDividedDifference b p))) := by
      rw [hrootB]
    _ = consecutiveLongRoot a b *
          (adjacentRootPolynomial a *
            adjacentDividedDifference a (adjacentDividedDifference b p)) -
        adjacentVariableSwap b
          (consecutiveLongRoot a b *
            (adjacentRootPolynomial a *
              adjacentDividedDifference a (adjacentDividedDifference b p))) := by
      rw [hfirstSwap]
      ring
    _ = consecutiveLongRoot a b *
          (adjacentDividedDifference b p -
            adjacentVariableSwap a (adjacentDividedDifference b p)) -
        adjacentVariableSwap b
          (consecutiveLongRoot a b *
            (adjacentDividedDifference b p -
              adjacentVariableSwap a (adjacentDividedDifference b p))) := by
      rw [hrootA]
    _ = p - adjacentVariableSwap b p - adjacentVariableSwap a p +
        adjacentVariableSwap a (adjacentVariableSwap b p) +
        adjacentVariableSwap b (adjacentVariableSwap a p) -
        adjacentVariableSwap b
          (adjacentVariableSwap a (adjacentVariableSwap b p)) := by
      rw [hmiddleSwap, hmiddle]
      ring

/-- The scaled three-letter divided-difference operator is the six-term
antisymmetrizer.  This public form of the calculation is useful independently
of the braid relation, notably as the rank-three longest-operator formula. -/
theorem adjacentBraid_scaled
    (a b : AdjacentPosition n) (hab : a.right = b.left)
    (p : BorelPresentation.PolynomialRing n) :
    (adjacentRootPolynomial a * consecutiveLongRoot a b *
        adjacentRootPolynomial b) *
        adjacentDividedDifference a
          (adjacentDividedDifference b (adjacentDividedDifference a p)) =
      p - adjacentVariableSwap a p - adjacentVariableSwap b p +
        adjacentVariableSwap b (adjacentVariableSwap a p) +
        adjacentVariableSwap a (adjacentVariableSwap b p) -
        adjacentVariableSwap a
          (adjacentVariableSwap b (adjacentVariableSwap a p)) :=
  left_braid_scaled a b hab p

/-- Type-A adjacent braid relation for the integral divided-difference
operators. -/
theorem adjacentDividedDifference_braid
    (a b : AdjacentPosition n) (hab : a.right = b.left)
    (p : BorelPresentation.PolynomialRing n) :
    adjacentDividedDifference a
        (adjacentDividedDifference b (adjacentDividedDifference a p)) =
      adjacentDividedDifference b
        (adjacentDividedDifference a (adjacentDividedDifference b p)) := by
  apply mul_left_cancel₀ (adjacentVandermonde_ne_zero a b hab)
  rw [left_braid_scaled a b hab p, right_braid_scaled a b hab p]
  rw [adjacentVariableSwap_braid a b hab p]
  ring

/-- Two adjacent positions are separated when their two-element supports are
disjoint.  For adjacent intervals this is equivalent to a gap in one of the
two possible orders. -/
def SeparatedAdjacentPositions (a b : AdjacentPosition n) : Prop :=
  a.right < b.left ∨ b.right < a.left

theorem separated_endpoint_ne
    (a b : AdjacentPosition n) (h : SeparatedAdjacentPositions a b) :
    a.left ≠ b.left ∧ a.left ≠ b.right ∧
      a.right ≠ b.left ∧ a.right ≠ b.right := by
  rcases h with h | h
  · exact ⟨(a.left_lt_right.trans h).ne,
      (a.left_lt_right.trans (h.trans b.left_lt_right)).ne,
      h.ne, (h.trans b.left_lt_right).ne⟩
  · exact ⟨(b.left_lt_right.trans h).ne.symm,
      h.ne.symm,
      (b.left_lt_right.trans (h.trans a.left_lt_right)).ne.symm,
      (h.trans a.left_lt_right).ne.symm⟩

set_option linter.unusedSimpArgs false in
/-- Disjoint adjacent transpositions commute as permutations. -/
theorem adjacentTransposition_commute_of_separated
    (a b : AdjacentPosition n) (h : SeparatedAdjacentPositions a b) :
    (adjacentTransposition a : Fin n → Fin n) ∘ adjacentTransposition b =
      (adjacentTransposition b : Fin n → Fin n) ∘ adjacentTransposition a := by
  obtain ⟨halbl, halbr, harbl, harbr⟩ :=
    separated_endpoint_ne a b h
  funext k
  by_cases hkal : k = a.left
  · subst k
    simp [adjacentTransposition, Equiv.swap_apply_def,
      halbl, halbr, harbl, harbr,
      halbl.symm, halbr.symm, harbl.symm, harbr.symm]
  · by_cases hkar : k = a.right
    · subst k
      simp [adjacentTransposition, Equiv.swap_apply_def,
        halbl, halbr, harbl, harbr,
        halbl.symm, halbr.symm, harbl.symm, harbr.symm]
    · by_cases hkbl : k = b.left
      · subst k
        simp [adjacentTransposition, Equiv.swap_apply_def,
          halbl, halbr, harbl, harbr,
          halbl.symm, halbr.symm, harbl.symm, harbr.symm]
      · by_cases hkbr : k = b.right
        · subst k
          simp [adjacentTransposition, Equiv.swap_apply_def,
            halbl, halbr, harbl, harbr,
            halbl.symm, halbr.symm, harbl.symm, harbr.symm]
        · simp [adjacentTransposition,
            Equiv.swap_apply_def, hkal, hkar, hkbl, hkbr]

/-- Variable swaps at separated adjacent positions commute. -/
theorem adjacentVariableSwap_commute_of_separated
    (a b : AdjacentPosition n) (h : SeparatedAdjacentPositions a b)
    (p : BorelPresentation.PolynomialRing n) :
    adjacentVariableSwap a (adjacentVariableSwap b p) =
      adjacentVariableSwap b (adjacentVariableSwap a p) := by
  simp only [adjacentVariableSwap, MvPolynomial.renameEquiv_apply]
  simp_rw [MvPolynomial.rename_rename]
  congr 2
  exact adjacentTransposition_commute_of_separated a b h

private theorem swap_root_of_separated
    (a b : AdjacentPosition n) (h : SeparatedAdjacentPositions a b) :
    adjacentVariableSwap a (adjacentRootPolynomial b) =
      adjacentRootPolynomial b := by
  obtain ⟨halbl, halbr, harbl, harbr⟩ :=
    separated_endpoint_ne a b h
  rw [adjacentRootPolynomial, map_sub]
  rw [adjacentVariableSwap_X_other a b.left halbl.symm harbl.symm,
    adjacentVariableSwap_X_other a b.right halbr.symm harbr.symm]

/-- Type-A distant-commutation relation for the integral divided-difference
operators. -/
theorem adjacentDividedDifference_commute_of_separated
    (a b : AdjacentPosition n) (h : SeparatedAdjacentPositions a b)
    (p : BorelPresentation.PolynomialRing n) :
    adjacentDividedDifference a (adjacentDividedDifference b p) =
      adjacentDividedDifference b (adjacentDividedDifference a p) := by
  apply mul_left_cancel₀
    (mul_ne_zero (adjacentRootPolynomial_ne_zero a)
      (adjacentRootPolynomial_ne_zero b))
  have hrootA (q : BorelPresentation.PolynomialRing n) :
      adjacentRootPolynomial a * adjacentDividedDifference a q =
        q - adjacentVariableSwap a q :=
    adjacentRoot_mul_adjacentDividedDifference a q
  have hrootB (q : BorelPresentation.PolynomialRing n) :
      adjacentRootPolynomial b * adjacentDividedDifference b q =
        q - adjacentVariableSwap b q :=
    adjacentRoot_mul_adjacentDividedDifference b q
  calc
    (adjacentRootPolynomial a * adjacentRootPolynomial b) *
        adjacentDividedDifference a (adjacentDividedDifference b p) =
      adjacentRootPolynomial b *
        (adjacentRootPolynomial a *
          adjacentDividedDifference a (adjacentDividedDifference b p)) := by
            ring
    _ = adjacentRootPolynomial b *
        (adjacentDividedDifference b p -
          adjacentVariableSwap a (adjacentDividedDifference b p)) := by
            rw [hrootA]
    _ = adjacentRootPolynomial b * adjacentDividedDifference b p -
        adjacentVariableSwap a
          (adjacentRootPolynomial b * adjacentDividedDifference b p) := by
      rw [map_mul, swap_root_of_separated a b h]
      ring
    _ = (p - adjacentVariableSwap b p) -
        adjacentVariableSwap a (p - adjacentVariableSwap b p) := by
      rw [hrootB p]
    _ = p - adjacentVariableSwap a p - adjacentVariableSwap b p +
        adjacentVariableSwap a (adjacentVariableSwap b p) := by
      rw [map_sub]
      ring
    _ = p - adjacentVariableSwap b p - adjacentVariableSwap a p +
        adjacentVariableSwap b (adjacentVariableSwap a p) := by
      rw [adjacentVariableSwap_commute_of_separated a b h p]
      ring
    _ = adjacentRootPolynomial a * adjacentDividedDifference a p -
        adjacentVariableSwap b
          (adjacentRootPolynomial a * adjacentDividedDifference a p) := by
      rw [hrootA p]
      rw [map_sub]
      ring
    _ = adjacentRootPolynomial a *
        (adjacentDividedDifference a p -
          adjacentVariableSwap b (adjacentDividedDifference a p)) := by
      rw [map_mul,
        swap_root_of_separated b a (h.elim Or.inr Or.inl)]
      ring
    _ = (adjacentRootPolynomial a * adjacentRootPolynomial b) *
        adjacentDividedDifference b (adjacentDividedDifference a p) := by
      rw [← hrootB]
      ring

end

end Schubert

end Schubert
