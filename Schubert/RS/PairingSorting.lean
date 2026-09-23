import Schubert.RS.RectangleCoefficient
import Schubert.RS.LaurentPrefixSupport

/-! Terminating sorting transfer and the off-diagonal dominant pairing. -/

namespace Schubert.RS
noncomputable section
open FinPermutation
variable {n : ℕ}

/-- Move every sorting operator from the first key to the second. The
second index remains a permutation of its original composition. -/
theorem pairing_sorting_transfer (a b : Composition n) :
    ∃ (u v : Composition n) (σ τ : Equiv.Perm (Fin n)),
      Antitone u ∧ a = (fun i => u (σ i)) ∧ v = (fun i => b (τ i)) ∧
      keyAtomPairing (key a) (key b) = keyAtomPairing (compositionMonomial u) (key v) := by
  induction a using (measure sortingMeasure).wf.induction generalizing b with
  | h a ih =>
    by_cases ha : (ascentSet a).Nonempty
    · let i := firstAscent a ha
      have hi := firstAscent_lt a ha
      by_cases hb : b (mirrorAdjacent i).right < b (mirrorAdjacent i).left
      · obtain ⟨u, v, σ, τ, hu, hσ, hτ, hp⟩ :=
          ih _ (sortingMeasure_swap_lt a i hi) (swapComposition b (mirrorAdjacent i))
        refine ⟨u, v, (adjacentTransposition i).trans σ,
          τ.trans (adjacentTransposition (mirrorAdjacent i)), hu, ?_, ?_, ?_⟩
        · funext j
          have he := congrFun hσ (adjacentTransposition i j)
          simpa [swapComposition, adjacentTransposition] using he
        · simpa [swapComposition] using hτ
        · rw [key_ascent a ha, keyAtomPairing_isobaric, isobaric_key, if_pos hb]
          exact hp
      · obtain ⟨u, v, σ, τ, hu, hσ, hτ, hp⟩ :=
          ih _ (sortingMeasure_swap_lt a i hi) b
        refine ⟨u, v, (adjacentTransposition i).trans σ, τ, hu, ?_, hτ, ?_⟩
        · funext j
          have he := congrFun hσ (adjacentTransposition i j)
          simpa [swapComposition, adjacentTransposition] using he
        · rw [key_ascent a ha, keyAtomPairing_isobaric, isobaric_key, if_neg hb]
          exact hp
    · refine ⟨a, b, Equiv.refl _, Equiv.refl _, antitone_of_no_ascent a ha,
        rfl, rfl, ?_⟩
      rw [key_of_no_ascent a ha]

/-- Support and adjointness force every nonzero dominant pairing to have
the reversed index. This includes repeated entries and ranks zero and one. -/
theorem dominant_pairing_index
    (hs : ∀ a : Composition n, PrefixSupported (fun i => (a i : ℤ)) (toLaurent (key a)))
    (u : Composition n) (hu : Antitone u) (a : Composition n)
    (hp : keyAtomPairing (key a) (compositionMonomial u) ≠ 0) :
    a = (fun i => u i.rev) := by
  have h₁ := pairing_monomial_support_bound (key a) _ (hs a) u hp
  obtain ⟨l, v, σ, τ, hl, hσ, hτ, he⟩ := pairing_sorting_transfer a u
  rw [key_of_antitone u hu] at he
  have hp' : keyAtomPairing (key v) (compositionMonomial l) ≠ 0 := by
    rw [keyAtomPairing_symmetric, ← he]
    exact hp
  have h₂ := pairing_monomial_support_bound (key v) _ (hs v) l hp'
  have h₃ : PrefixLE (fun i => (l i.rev : ℤ)) (fun i => (a i : ℤ)) := by
    rw [hσ]
    exact prefixLE_reverse_dominant l hl σ
  have h₄ : PrefixLE (fun i => (u i.rev : ℤ)) (fun i => (v i : ℤ)) := by
    rw [hτ]
    exact prefixLE_reverse_dominant u hu τ
  have heq := h₁.antisymm (h₄.trans (h₂.trans h₃))
  funext i
  have hi := congrFun heq i
  exact_mod_cast hi

end
end Schubert.RS
