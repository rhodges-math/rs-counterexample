import Schubert.TypeA.Permutations.SubwordToRank

/-!
# Full type-A Bruhat rank-matrix / reduced-subword criterion

The first theorem uses the repository's right-sorting convention. The
second reverses that word to the product-from-identity
convention. Both hold for every reduced upper adjacent word, without a
chosen-word restriction, and for all finite ranks including `n=0,1`.
-/

namespace Schubert.FinPermutation

variable {n : ℕ}

theorem strongBruhatLE_iff_reduced_sorting_subword
    (u v : FinPermutation n) (word : List (AdjacentPosition n))
    (hprod : applyRightAdjacentWord word v = Equiv.refl (Fin n))
    (hlen : word.length = v.length) :
    u ≤ᴮ v ↔
      ∃ sub : List (AdjacentPosition n),
        sub.Sublist word ∧
        applyRightAdjacentWord sub u = Equiv.refl (Fin n) ∧
        sub.length = u.length := by
  constructor
  · exact reduced_sorting_subword_of_strongBruhatLE u v word hprod hlen
  · rintro ⟨sub, hsub, hsubprod, hsublen⟩
    exact strongBruhatLE_of_reduced_sorting_subword u v word sub
      hprod hlen hsub hsubprod hsublen

/-- A reduced adjacent expression for `v` contains a
reduced adjacent expression for `u` exactly when the southwest rank
matrix of `u` is pointwise bounded by that of `v`. The expression is
evaluated by `applyRightAdjacentWord word 1`; this explicitly fixes the
right-position-swap/list-fold orientation. -/
theorem strongBruhatLE_iff_reduced_adjacent_subword
    (u v : FinPermutation n) (word : List (AdjacentPosition n))
    (hprod : applyRightAdjacentWord word (Equiv.refl (Fin n)) = v)
    (hlen : word.length = v.length) :
    u ≤ᴮ v ↔
      ∃ sub : List (AdjacentPosition n),
        sub.Sublist word ∧
        applyRightAdjacentWord sub (Equiv.refl (Fin n)) = u ∧
        sub.length = u.length := by
  have hsort := (reduced_product_iff_reduced_sorting_reverse v word).mp
    ⟨hprod, hlen⟩
  have hiff := strongBruhatLE_iff_reduced_sorting_subword u v
    word.reverse hsort.1 hsort.2
  constructor
  · intro huv
    obtain ⟨sub, hsub, hsubsort, hsublen⟩ := hiff.mp huv
    have hword := (reduced_product_iff_reduced_sorting_reverse
      u sub.reverse).mpr ⟨by simpa using hsubsort, by simpa using hsublen⟩
    exact ⟨sub.reverse, by simpa using hsub.reverse,
      hword.1, hword.2⟩
  · rintro ⟨sub, hsub, hsubprod, hsublen⟩
    have hsubsort := (reduced_product_iff_reduced_sorting_reverse
      u sub).mp ⟨hsubprod, hsublen⟩
    apply hiff.mpr
    exact ⟨sub.reverse, hsub.reverse, hsubsort.1, hsubsort.2⟩

end Schubert.FinPermutation
