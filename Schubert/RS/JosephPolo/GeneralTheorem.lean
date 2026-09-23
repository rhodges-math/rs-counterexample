import Schubert.RS.JosephPolo.TableauCounting
import Schubert.RS.JosephPolo.CountingCriterion

namespace Schubert.RS.Representation
noncomputable section

/-- The Joseph-Polo presentation and Demazure character formula for every
composition flag module, by simultaneous induction using tableau-string counts. -/
theorem compositionFlagJP_and_character {n : ℕ} (u : Composition n) :
    CompositionFlagJosephPolo u ∧ HasTorusCharacter (compositionFlagTorus u) (key u) :=
  compositionFlagJP_character_of_chain_count composition_chain_count u

theorem compositionFlagJosephPolo {n : ℕ} (u : Composition n) :
    CompositionFlagJosephPolo u :=
  (compositionFlagJP_and_character u).1

theorem compositionPresentationMap_bijective {n : ℕ} (u : Composition n) :
    Function.Bijective (compositionPresentationMap u) :=
  ⟨(compositionFlagJosephPolo_iff_injective u).mp (compositionFlagJosephPolo u),
    compositionPresentationMap_surjective u⟩

theorem compositionFlagDemazureCharacter {n : ℕ} (u : Composition n) :
    CompositionFlagDemazureCharacter u :=
  (compositionFlagDemazureCharacter_iff_character u).mpr (compositionFlagJP_and_character u).2

end
end Schubert.RS.Representation
