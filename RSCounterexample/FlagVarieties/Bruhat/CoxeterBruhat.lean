import RSCounterexample.FlagVarieties.Bruhat.Coxeter
import TauCeti.GroupTheory.Coxeter.Bruhat

/-!
# The rank-matrix order is the Bruhat order of the Coxeter system

**`bruhatLE_iff_strongBruhatLE`**: for the Coxeter system `permCoxeterSystem n` of type `A_n` on
`S_{n+1}`, Tau Ceti's Bruhat order `CoxeterSystem.BruhatLE` (the reachability order of the Bruhat
graph) is the rank-matrix order `≤ᴮ` of the library. Both are the subword order of a reduced word:
Tau Ceti's subword property (`CoxeterSystem.bruhatLE_iff_exists_sublist_wordProd_eq`, with the
deletion condition `CoxeterSystem.exists_isReduced_sublist`) on one side, and
`strongBruhatLE_iff_exists_reduced_sublist` on the other.
-/

namespace FlagVarieties.Bruhat

open Schubert Schubert.FinPermutation

variable {n : ℕ}

/-- **Tau Ceti's Coxeter Bruhat order on `S_{n+1}` is the rank-matrix order.** -/
theorem bruhatLE_iff_strongBruhatLE (u v : Equiv.Perm (Fin (n + 1))) :
    (permCoxeterSystem n).BruhatLE u v ↔ u ≤ᴮ v := by
  obtain ⟨ω, hω, rfl⟩ := (permCoxeterSystem n).exists_isReduced v
  rw [CoxeterSystem.bruhatLE_iff_exists_sublist_wordProd_eq (cs := permCoxeterSystem n) hω,
    strongBruhatLE_iff_exists_reduced_sublist u hω]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨σ', hσ', hred, hprod⟩ :=
      CoxeterSystem.exists_isReduced_sublist (cs := permCoxeterSystem n) σ
    exact ⟨σ', hσ'.trans hσ, hred, hprod⟩
  · rintro ⟨σ, hσ, -, hprod⟩
    exact ⟨σ, hσ, hprod⟩

/-- The Bruhat partial order of the Coxeter system is the rank-matrix order. -/
theorem bruhatPartialOrder_le_iff (u v : Equiv.Perm (Fin (n + 1))) :
    (permCoxeterSystem n).bruhatPartialOrder.le u v ↔ u ≤ᴮ v := by
  rw [CoxeterSystem.bruhatPartialOrder_le]
  exact bruhatLE_iff_strongBruhatLE u v

end FlagVarieties.Bruhat
