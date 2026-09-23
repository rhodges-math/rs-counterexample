import Schubert.RS.JosephPolo.TableauCharacterBase
import Schubert.RS.KeyAction

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation

private theorem isobaric_key_swap_of_le {n : ℕ} (u : Composition n)
    (i : AdjacentPosition n) (hu : u i.left ≤ u i.right) :
    isobaric i (key (swapComposition u i)) = key u := by
  by_cases he : u i.left = u i.right
  · have hs : swapComposition u i = u := by
      funext j
      by_cases ha : j = i.left
      · subst j; simpa only [swapComposition_left] using he.symm
      · by_cases hb : j = i.right
        · subst j; simpa only [swapComposition_right] using he
        · exact swapComposition_other u i j ha hb
    rw [hs,key_isobaric_of_equal u i he]
  · exact (key_any_ascent u i (lt_of_le_of_ne hu he)).symm

theorem flagTableauCharacter_symm_eq_key {n d : ℕ} (h : Fin d → Fin n)
    (v : FinPermutation n) :
    flagTableauCharacter h v.symm = key (extremalWeight (columnMultiplicity h) v.symm) := by
  generalize hl : v.length = l
  induction l using Nat.strong_induction_on generalizing v with
  | h l ih =>
    by_cases hvrefl : v = Equiv.refl (Fin n)
    · subst v
      change flagTableauCharacter h (Equiv.refl (Fin n)) = key (shapeWeight (columnMultiplicity h))
      rw [flagTableauCharacter_refl,key_of_antitone _ (shapeWeight_antitone _)]
    · obtain ⟨a,b,hb,hd⟩ := exists_descent_of_ne_refl v hvrefl
      let i : AdjacentPosition n := ⟨a,by rw [← hb]; exact b.isLt⟩
      have hv : v.HasDescent i.left := ⟨b,hb,hd⟩
      have hvd := (hasDescent_left_iff v i).mp hv
      have hvlt : (v.rightAdjacentSwap i).length < l := by
        have := length_rightAdjacentSwap_of_descent v i hv
        omega
      have he : FinPermutation.leftAdjacentSwap v.symm i = (v.rightAdjacentSwap i).symm := rfl
      have hx : extremalWeight (columnMultiplicity h) (v.rightAdjacentSwap i).symm =
          swapComposition (extremalWeight (columnMultiplicity h) v.symm) i := by
        exact extremalWeight_swap_mul (columnMultiplicity h) v.symm i.left i.right
      have hu : extremalWeight (columnMultiplicity h) v.symm i.left ≤
          extremalWeight (columnMultiplicity h) v.symm i.right :=
        shapeWeight_antitone (columnMultiplicity h) hvd.le
      rw [← flagTableauCharacter_recursion h i v.symm hvd,he,
        ih (v.rightAdjacentSwap i).length hvlt (v.rightAdjacentSwap i) rfl,hx]
      exact isobaric_key_swap_of_le _ i hu

/-- The defining-chain generating polynomial equals the key polynomial
for every shape, permutation, and column order. -/
theorem flagTableauCharacter_eq_key {n d : ℕ} (h : Fin d → Fin n)
    (w : FinPermutation n) :
    flagTableauCharacter h w = key (extremalWeight (columnMultiplicity h) w) :=
  flagTableauCharacter_symm_eq_key h w.symm

end
end Schubert.RS.Representation
