import Schubert.RS.JosephPolo.CompletionDimension
import Schubert.RS.JosephPolo.StandardMonomialBound
import Schubert.RS.FlagCharacterInduction

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 200000

/-- A dimension bound implies Joseph-Polo and the character formula by
simultaneous induction, without using the JP-dependent general character theorem. -/
theorem compositionFlagJP_character_of_dimension_bound {n : ℕ}
    (hbound : ∀ u : Composition n, MvPolynomial.eval (fun _ => (1:ℤ)) (key u) ≤
      (Module.finrank ℂ (compositionFlag u) : ℤ)) :
    ∀ u : Composition n, CompositionFlagJosephPolo u ∧
      HasTorusCharacter (compositionFlagTorus u) (key u) := by
  intro u
  induction u using (measure sortingMeasure).wf.induction with
  | h u ih =>
    by_cases hu : Antitone u
    · exact ⟨compositionFlagJosephPolo_of_antitone u hu,
        (compositionFlagDemazureCharacter_iff_character u).mp (compositionFlagDemazureCharacter_of_antitone u hu)⟩
    · have ha : (ascentSet u).Nonempty := by
        by_contra hn
        exact hu (antitone_of_no_ascent u hn)
      let i := firstAscent u ha
      have hi : u i.left < u i.right := firstAscent_lt u ha
      have hsmaller := ih (swapComposition u i) (sortingMeasure_swap_lt u i hi)
      obtain ⟨B⟩ := exists_compositionRootStringBasis (swapComposition u i) (adjacentPositiveRoot i)
      have hbij := B.adjacentEvaluation_bijective_of_dimension_bound u i hi hsmaller.2 (hbound u)
      have hJP := (compositionFlagJosephPolo_iff_adjacent_evaluation_injective u i hi B hsmaller.1).mpr hbij.1
      refine ⟨hJP,?_⟩
      obtain ⟨p,hp,hp'⟩ := B.adjacent_character_of_bijective u i (B.adjacentEvaluation u i hi)
        (B.adjacentEvaluation_boundary u i hi) (B.adjacentEvaluation_lowering u i hi) hbij
      rw [hp.unique hsmaller.2,← key_any_ascent u i hi] at hp'
      exact hp'

/-- A defining-chain count supplies the dimension bound for the simultaneous
Joseph-Polo and character-formula induction. -/
theorem compositionFlagJP_character_of_chain_count {n : ℕ}
    (hcount : ∀ u : Composition n, ∃ (d : ℕ) (h : Fin d → Fin n),
      columnMultiplicity h = compositionShape u ∧
      MvPolynomial.eval (fun _ => (1:ℤ)) (key u) ≤
        (Fintype.card {T : (j : Fin d) → FlagMinorRowSet (h j) //
          HasFlagDefiningChain h T (compositionPermutation u)} : ℤ)) :
    ∀ u : Composition n, CompositionFlagJosephPolo u ∧
      HasTorusCharacter (compositionFlagTorus u) (key u) := by
  apply compositionFlagJP_character_of_dimension_bound
  intro u
  obtain ⟨d,h,hshape,hcard⟩ := hcount u
  have hdim := flagDefiningChain_card_le_finrank h (compositionPermutation u)
  rw [hshape] at hdim
  exact hcard.trans (by exact_mod_cast hdim)

end
end Schubert.RS.Representation
