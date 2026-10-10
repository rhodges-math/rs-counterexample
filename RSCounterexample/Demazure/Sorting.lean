import RSCounterexample.Demazure.Keys
import Mathlib.Order.Fin.Basic

/-!
# Ascents of compositions

Swapping an adjacent pair preserves the degree of a composition (`swapComposition_degree`), and a
composition has no ascent if and only if it is antitone (`no_ascent_iff_antitone`).
-/

open Schubert

namespace Demazure

open FinPermutation
variable {n : ℕ}

theorem swapComposition_degree (a : Composition n) (i : AdjacentPosition n) :
    (∑ j, swapComposition a i j) = ∑ j, a j := by
  apply Fintype.sum_equiv (adjacentTransposition i)
  intro j
  rfl

theorem antitone_of_no_ascent (a : Composition n) (h : ¬(ascentSet a).Nonempty) :
    Antitone a := by
  cases n with
  | zero => intro i; exact Fin.elim0 i
  | succ n =>
    apply Fin.antitone_iff_succ_le.mpr
    intro j
    by_contra hj
    apply h
    refine ⟨j, ?_⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, lt_of_not_ge hj⟩

theorem no_ascent_iff_antitone (a : Composition n) :
    ¬(ascentSet a).Nonempty ↔ Antitone a :=
  ⟨antitone_of_no_ascent a, no_ascent_of_antitone a⟩

end Demazure
