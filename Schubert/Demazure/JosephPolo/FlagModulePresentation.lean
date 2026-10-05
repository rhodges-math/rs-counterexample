import Schubert.Demazure.JosephPolo.TableauCounting
import Schubert.Demazure.JosephPolo.CountingCriterion

/-!
# The Joseph–Polo presentation of flag modules

Every composition flag module has the Joseph–Polo presentation and the Demazure character
(`compositionFlagJosephPolo_and_character`): the canonical map from the presentation quotient onto
the flag module is bijective (`compositionPresentationMap_bijective`), and the torus character is
the key polynomial (`compositionFlagDemazureCharacter`).
-/

open Schubert

namespace Demazure.FlagModule
noncomputable section

/-- The Joseph-Polo presentation and Demazure character formula for every
composition flag module, by simultaneous induction using tableau-string counts. -/
theorem compositionFlagJosephPolo_and_character {n : ℕ} (u : Composition n) :
    CompositionFlagJosephPolo u ∧ HasTorusCharacter (compositionFlagTorus u) (key u) :=
  compositionFlagJosephPolo_character_of_chain_count composition_chain_count u

theorem compositionFlagJosephPolo {n : ℕ} (u : Composition n) :
    CompositionFlagJosephPolo u :=
  (compositionFlagJosephPolo_and_character u).1

theorem compositionPresentationMap_bijective {n : ℕ} (u : Composition n) :
    Function.Bijective (compositionPresentationMap u) :=
  ⟨(compositionFlagJosephPolo_iff_injective u).mp (compositionFlagJosephPolo u),
    compositionPresentationMap_surjective u⟩

theorem compositionFlagDemazureCharacter {n : ℕ} (u : Composition n) :
    CompositionFlagDemazureCharacter u :=
  (compositionFlagDemazureCharacter_iff_character u).mpr
      (compositionFlagJosephPolo_and_character u).2

end
end Demazure.FlagModule
