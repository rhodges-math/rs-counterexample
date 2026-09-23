import Schubert.RS.Keys
import Mathlib.Order.Fin.Basic

namespace Schubert.RS

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

end Schubert.RS
