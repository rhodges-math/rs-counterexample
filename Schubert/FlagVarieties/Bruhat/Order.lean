import Schubert.TypeA.Permutations.RankSubwordCriterion
import Schubert.FlagVarieties.Normality.Fulton.Grassmannian

/-!
# Bruhat orders on `S_n`

The library compares permutations with the **rank-matrix order** `u ≤ᴮ v`
(`Schubert.FinPermutation.StrongBruhatLE`: `r_u(p, q) ≤ r_v(p, q)` for all `p`, `q`). This file
collects its equivalent descriptions.

* **Tableau criterion** (`FlagVarieties.PointModel.strongBruhat_iff_galeLE`): `u ≤ᴮ v` iff
  `u{0..k} ≤ v{0..k}` in the Gale order for every `k`.
* **Subword order** (`SubwordLE`): `u` is the product of a reduced subword of a reduced word for
  `v`. `strongBruhatLE_iff_subwordLE`: it is the rank-matrix order; moreover
  `strongBruhatLE_iff_of_reduced`: every reduced word for `v` may be used. This is the type-A
  reduced-subword criterion (`Schubert/TypeA/Permutations/RankSubwordCriterion`).
* Length: `length_le_of_strongBruhatLE`, `eq_of_strongBruhatLE_of_length_eq` (`Schubert.TypeA`).

Words are evaluated as `applyRightAdjacentWord word 1`, a product of adjacent transpositions
acting on positions.
-/

namespace FlagVarieties.Bruhat

open Schubert Schubert.FinPermutation

variable {n : ℕ}

/-- **The subword order**: some reduced word for `v` contains a reduced word for `u` as a
sublist. -/
def SubwordLE (u v : FinPermutation n) : Prop :=
  ∃ word sub : List (AdjacentPosition n),
    applyRightAdjacentWord word (Equiv.refl (Fin n)) = v ∧ word.length = v.length ∧
      sub.Sublist word ∧ applyRightAdjacentWord sub (Equiv.refl (Fin n)) = u ∧
        sub.length = u.length

/-- Every permutation has a reduced word. -/
theorem exists_reduced_word (v : FinPermutation n) :
    ∃ word : List (AdjacentPosition n),
      applyRightAdjacentWord word (Equiv.refl (Fin n)) = v ∧ word.length = v.length := by
  obtain ⟨word, hprod, hlen⟩ := exists_reducedWord_to_refl v
  refine ⟨word.reverse, (reduced_product_iff_reduced_sorting_reverse v word.reverse).mpr ?_⟩
  rw [List.reverse_reverse]
  exact ⟨hprod, hlen⟩

/-- **The rank-matrix order is the subword order.** -/
theorem strongBruhatLE_iff_subwordLE (u v : FinPermutation n) : u ≤ᴮ v ↔ SubwordLE u v := by
  constructor
  · intro huv
    obtain ⟨word, hprod, hlen⟩ := exists_reduced_word v
    obtain ⟨sub, hsub, hsubprod, hsublen⟩ :=
      (strongBruhatLE_iff_reduced_adjacent_subword u v word hprod hlen).mp huv
    exact ⟨word, sub, hprod, hlen, hsub, hsubprod, hsublen⟩
  · rintro ⟨word, sub, hprod, hlen, hsub, hsubprod, hsublen⟩
    exact (strongBruhatLE_iff_reduced_adjacent_subword u v word hprod hlen).mpr
      ⟨sub, hsub, hsubprod, hsublen⟩

/-- **Independence of the reduced word**: for any reduced word of `v`, `u ≤ᴮ v` iff that word
contains a reduced word for `u`. -/
theorem strongBruhatLE_iff_of_reduced (u v : FinPermutation n) (word : List (AdjacentPosition n))
    (hprod : applyRightAdjacentWord word (Equiv.refl (Fin n)) = v)
    (hlen : word.length = v.length) :
    u ≤ᴮ v ↔ ∃ sub : List (AdjacentPosition n), sub.Sublist word ∧
      applyRightAdjacentWord sub (Equiv.refl (Fin n)) = u ∧ sub.length = u.length :=
  strongBruhatLE_iff_reduced_adjacent_subword u v word hprod hlen

/-- **Tableau criterion** (re-exported): `u ≤ᴮ v` iff all prefixes compare in the Gale order. -/
theorem strongBruhatLE_iff_galeLE (u v : Equiv.Perm (Fin n)) :
    u ≤ᴮ v ↔ ∀ k, PointModel.galeLE (Demazure.FlagModule.flagPrefixRows u k)
      (Demazure.FlagModule.flagPrefixRows v k) :=
  PointModel.strongBruhat_iff_galeLE

end FlagVarieties.Bruhat
