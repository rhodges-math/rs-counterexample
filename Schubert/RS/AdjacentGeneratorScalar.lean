import Schubert.RS.Representation.StringEndpoints

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation

theorem compositionFlagGenerator_swap_line {n : ℕ} (u : Composition n) (i : AdjacentPosition n) :
    ∃ c : ℂ, c≠0 ∧ (compositionFlagGenerator (swapComposition u i)).val=
      c • rowRename (Equiv.swap i.left i.right) (compositionFlagGenerator u).val := by
  have hs : compositionShape (swapComposition u i)=compositionShape u :=
    compositionShape_perm u (Equiv.swap i.left i.right)
  have hw : extremalWeight (compositionShape u) (Equiv.swap i.left i.right * compositionPermutation u)=
      extremalWeight (compositionShape u) (compositionPermutation (swapComposition u i)) := by
    rw [extremalWeight_swap_mul,composition_extremalWeight,← hs,composition_extremalWeight]
    rfl
  obtain ⟨c,hc,he⟩ := extremalFlag_line_of_weight_eq (compositionShape u)
    (Equiv.swap i.left i.right * compositionPermutation u)
    (compositionPermutation (swapComposition u i)) hw
  refine ⟨c,hc,?_⟩
  change extremalFlag (compositionShape (swapComposition u i))
    (compositionPermutation (swapComposition u i))=_
  rw [hs,he]
  change c • rowRename (Equiv.swap i.left i.right * compositionPermutation u)
    (highestFlag (compositionShape u))=_
  rw [rowRename_mul]
  rfl

/-- The actual canonical target generator is a nonzero scalar multiple
of the terminal lowering vector of the canonical neighboring generator.
Possible signs from tied entries and canonical permutation choices are retained. -/
theorem compositionFlagGenerator_reverse_scalar {n : ℕ} (u : Composition n)
    (i : AdjacentPosition n) (hu : u i.left<u i.right) :
    ∃ c : ℂ, c≠0 ∧ (compositionFlagGenerator u).val=
      c • derivationIter (matrixUnitDerivation i.right i.left) (u i.right-u i.left)
        (compositionFlagGenerator (swapComposition u i)).val := by
  obtain ⟨c,hc,he⟩ := extremalFlag_reverse_string (compositionShape u) (compositionPermutation u)
    i.left i.right (by simpa only [composition_extremalWeight] using hu)
  rw [composition_extremalWeight] at he
  obtain ⟨s,hs,hsg⟩ := compositionFlagGenerator_swap_line u i
  have hr : rowRename (Equiv.swap i.left i.right) (compositionFlagGenerator u).val=
      s⁻¹ • (compositionFlagGenerator (swapComposition u i)).val := by
    rw [hsg,smul_smul,inv_mul_cancel₀ hs,one_smul]
  change (compositionFlagGenerator u).val=c • derivationIter _ _
    (rowRename (Equiv.swap i.left i.right) (compositionFlagGenerator u).val) at he
  rw [hr] at he
  change (compositionFlagGenerator u).val=c •
    ((matrixUnitDerivation i.right i.left).toLinearMap^(u i.right-u i.left))
      (s⁻¹ • (compositionFlagGenerator (swapComposition u i)).val) at he
  rw [map_smul,smul_smul] at he
  exact ⟨c*s⁻¹,mul_ne_zero hc (inv_ne_zero hs),he⟩

end
end Schubert.RS.Representation
