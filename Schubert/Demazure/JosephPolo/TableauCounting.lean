import Schubert.Demazure.JosephPolo.TableauKeys
import Schubert.Demazure.JosephPolo.ColumnRealization

/-!
# Counting defining chains by keys

The value at `1` of the tableau character counts the tuples with a defining chain, so this number is
the value at `1` of the key polynomial (`flagDefiningChain_card_eq_key_eval`). For every composition
`u` some column order realizes the shape of `u` with at least `key u (1)` such tuples
(`composition_chain_count`).
-/

open Schubert

namespace Demazure.FlagModule
noncomputable section
open FinPermutation
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem flagTableauCharacter_eval_one {n d : ℕ} (h : Fin d → Fin n)
    (w : FinPermutation n) :
    MvPolynomial.eval (fun _ => (1:ℤ)) (flagTableauCharacter h w) =
      (Fintype.card {T : (j : Fin d) → FlagMinorRowSet (h j) // HasFlagDefiningChain h T w} :
          ℤ) := by
  classical
  simp [flagTableauCharacter,compositionMonomial,Fintype.card_subtype,apply_ite,
    MvPolynomial.eval_monomial]

/-- Exact enumeration of the defining-chain tuples by a key evaluated at 1. -/
theorem flagDefiningChain_card_eq_key_eval {n d : ℕ} (h : Fin d → Fin n)
    (w : FinPermutation n) :
    (Fintype.card {T : (j : Fin d) → FlagMinorRowSet (h j) // HasFlagDefiningChain h T w} : ℤ) =
      MvPolynomial.eval (fun _ => (1:ℤ)) (key (extremalWeight (columnMultiplicity h) w)) := by
  rw [← flagTableauCharacter_eval_one,flagTableauCharacter_eq_key]

theorem composition_chain_count {n : ℕ} (u : Composition n) :
    ∃ (d : ℕ) (h : Fin d → Fin n), columnMultiplicity h = compositionShape u ∧
      MvPolynomial.eval (fun _ => (1:ℤ)) (key u) ≤
        (Fintype.card {T : (j : Fin d) → FlagMinorRowSet (h j) //
          HasFlagDefiningChain h T (compositionPermutation u)} : ℤ) := by
  obtain ⟨d,h,hm⟩ := exists_columnMultiplicity (compositionShape u)
  refine ⟨d,h,hm,?_⟩
  have hc := flagDefiningChain_card_eq_key_eval h (compositionPermutation u)
  rw [hm,composition_extremalWeight] at hc
  exact hc.symm.le

end
end Demazure.FlagModule
