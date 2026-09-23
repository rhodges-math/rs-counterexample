import Schubert.RS.PairingAdjoint

/-! # Induction for global key-atom orthogonality

The induction step reduces orthogonality to the dominant base pairing.
The base pairing is an explicit hypothesis here and is proved in GlobalDuality.
-/

namespace Schubert.RS

open FinPermutation
noncomputable section
variable {n : ℕ}

theorem reverse_swapComposition (a : Composition n) (i : AdjacentPosition n) :
    (fun k => swapComposition a i k.rev) =
      swapComposition (fun k => a k.rev) (mirrorAdjacent i) := by
  funext k
  have h := adjacentTransposition_mirror (mirrorAdjacent i) k
  simp only [mirrorAdjacent_involutive] at h
  exact congrArg a h

theorem pairing_orthogonality_step (u : Composition n) (i : AdjacentPosition n)
    (hu : u i.left < u i.right)
    (ih : ∀ a : Composition n, keyAtomPairing (key a) (atom (swapComposition u i)) =
      if a = (fun k => swapComposition u i k.rev) then 1 else 0)
    (a : Composition n) :
    keyAtomPairing (key a) (atom u) = if a = (fun k => u k.rev) then 1 else 0 := by
  rw [keyAtomPairing_key_atom_ascent a u i hu]
  by_cases hd : a (mirrorAdjacent i).right < a (mirrorAdjacent i).left
  · rw [if_pos hd, ih, ih]
    have hn : a ≠ (fun k => swapComposition u i k.rev) := by
      intro h
      subst a
      simp only [mirrorAdjacent_left, mirrorAdjacent_right, Fin.rev_rev,
        swapComposition_left, swapComposition_right] at hd
      omega
    rw [if_neg hn, sub_zero, reverse_swapComposition]
    have he : swapComposition a (mirrorAdjacent i) =
        swapComposition (fun k => u k.rev) (mirrorAdjacent i) ↔ a = (fun k => u k.rev) := by
      constructor
      · intro h
        simpa using congrArg (fun b => swapComposition b (mirrorAdjacent i)) h
      · intro h
        rw [h]
    simp only [he]
  · rw [if_neg hd]
    have hn : a ≠ (fun k => u k.rev) := by
      intro h
      subst a
      simp only [mirrorAdjacent_left, mirrorAdjacent_right, Fin.rev_rev] at hd
      exact hd hu
    rw [if_neg hn]

/-- Conditional assembly of the induction; the named dominant base is
explicitly open and must be proved before this can certify duality. -/
theorem keyAtom_orthogonality_of_dominant
    (dominant_base : ∀ u : Composition n, Antitone u → ∀ a : Composition n,
      keyAtomPairing (key a) (compositionMonomial u) =
        if a = (fun k => u k.rev) then 1 else 0)
    (u a : Composition n) :
    keyAtomPairing (key a) (atom u) = if a = (fun k => u k.rev) then 1 else 0 := by
  induction u using (measure sortingMeasure).wf.induction generalizing a with
  | h u ih =>
    by_cases hu : (ascentSet u).Nonempty
    · let i := firstAscent u hu
      have hi := firstAscent_lt u hu
      exact pairing_orthogonality_step u i hi
        (ih _ (sortingMeasure_swap_lt u i hi)) a
    · rw [atom_of_no_ascent u hu]
      exact dominant_base u (antitone_of_no_ascent u hu) a

end
end Schubert.RS
