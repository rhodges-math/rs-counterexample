import RSCounterexample.Demazure.PBW.Spanning
import RSCounterexample.Demazure.PBW.PartialPairing
import RSCounterexample.Demazure.PBW.CenteredAction

/-!
# Ordered words of root operators

`powersWord order powers` is the word that lists each positive root as often as `powers` prescribes,
in the given root order. Its product is the ordered root monomial (`rootWord_powersWord`), and the
exponent of the word determines `powers` (`powersWord_exponent_injective`).
-/

open Schubert

namespace Demazure.FlagModule
noncomputable section
open Demazure.PBW

/-- The word listing each root `r` exactly `powers r` times, in the order of `order`. -/
def powersWord {n : ℕ} (order : RootOrdering n) (powers : PositiveRoot n → ℕ) :
    List (PositiveRoot n) := order.roots.flatMap fun r => List.replicate (powers r) r

theorem rootWord_powersWord {n : ℕ} (order : RootOrdering n) (powers : PositiveRoot n → ℕ) :
    rootWord (powersWord order powers) = orderedRootMonomial order powers := by
  rw [orderedRootMonomial_eq]
  unfold powersWord rootWord
  induction order.roots with
  | nil => simp
  | cons r rs ih => simp [ih]

private theorem replicated_count {α : Type*} [DecidableEq α] [BEq α] [LawfulBEq α]
    (order : List α) (powers : α → ℕ) (hn : order.Nodup) (r : α) :
    (order.flatMap fun s => List.replicate (powers s) s).count r =
      if r ∈ order then powers r else 0 := by
  induction order with
  | nil => simp
  | cons s order ih =>
    have hs := List.nodup_cons.mp hn
    by_cases h : r = s
    · subst s; simp [ih hs.2, hs.1]
    · simp [List.flatMap_cons, ih hs.2, List.count_replicate, h, Ne.symm h]

theorem powersWord_count {n : ℕ} (order : RootOrdering n) (powers : PositiveRoot n → ℕ)
    (r : PositiveRoot n) : (powersWord order powers).count r = powers r := by
  classical
  unfold powersWord
  exact (replicated_count order.roots powers order.nodup r).trans (ite_eq_left (order.complete r))

theorem powersWord_exponent_injective {n : ℕ} (order : RootOrdering n) :
    Function.Injective (fun powers : PositiveRoot n → ℕ =>
      wordExponent rootCoordinate (powersWord order powers)) := by
  classical
  intro a b h
  funext r
  have hr := congrArg (fun e => e (rootCoordinate r)) h
  rw [wordExponent_apply_index rootCoordinate (rootCoordinate_injective n),
    wordExponent_apply_index rootCoordinate (rootCoordinate_injective n)] at hr
  exact (powersWord_count order a r).symm.trans (hr.trans (powersWord_count order b r))

end
end Demazure.FlagModule
