import Schubert.RS.DominantFlagCharacter
import Schubert.RS.Representation.CompositionStringFiltration

/-! A conditional induction for the Demazure character formula from a
root-string filtration property, with the dominant base case proved. -/

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation

theorem compositionFlagDemazureCharacter_iff_character {n : ℕ} (u : Composition n) :
    CompositionFlagDemazureCharacter u ↔ HasTorusCharacter (compositionFlagTorus u) (key u) := by
  constructor
  · intro h w
    exact (h w).2
  · intro h w
    exact ⟨inferInstance, h w⟩

/-- At each nondominant composition, one suitable adjacent filtration is
enough. The ascent may depend on the composition; no fixed sorting choice
or compatibility between different choices is required. -/
theorem compositionFlagDemazureCharacter_of_filtration_witnesses {n : ℕ}
    (hF : ∀ u : Composition n, ¬Antitone u →
      ∃ (i : AdjacentPosition n) (hi : u i.left < u i.right),
        CompositionStringFiltration u i hi) :
    ∀ u : Composition n, CompositionFlagDemazureCharacter u := by
  intro u
  induction u using (measure sortingMeasure).wf.induction with
  | h u ih =>
    by_cases hu : Antitone u
    · exact compositionFlagDemazureCharacter_of_antitone u hu
    · obtain ⟨i, hi, hfil⟩ := hF u hu
      apply (compositionFlagDemazureCharacter_iff_character u).mpr
      apply composition_character_ascent_of_string_filtration u i hi hfil
      exact (compositionFlagDemazureCharacter_iff_character _).mp
        (ih _ (sortingMeasure_swap_lt u i hi))

/-- A more restrictive first-ascent version, useful when constructions use
the same deterministic sorting recursion as the definition of keys. -/
theorem compositionFlagDemazureCharacter_of_first_ascent_filtrations {n : ℕ}
    (hF : ∀ (u : Composition n) (h : (ascentSet u).Nonempty),
      CompositionStringFiltration u (firstAscent u h) (firstAscent_lt u h)) :
    ∀ u : Composition n, CompositionFlagDemazureCharacter u := by
  apply compositionFlagDemazureCharacter_of_filtration_witnesses
  intro u hu
  have ha : (ascentSet u).Nonempty := by
    by_contra hn
    exact hu (antitone_of_no_ascent u hn)
  exact ⟨firstAscent u ha, firstAscent_lt u ha, hF u ha⟩

end
end Schubert.RS.Representation
