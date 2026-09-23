import Schubert.RS.JosephPolo.FlagStringWeights
import Schubert.RS.MonomialOperators
import Schubert.RS.Keys

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation Schubert
open scoped BigOperators

/-- The weight sum of a full column string is the isobaric image of
its head monomial. This uses only the polynomial operator formula. -/
theorem IsColumnWeightString.character {n L : ℕ} {i : AdjacentPosition n}
    {W : Fin (L+1) → Composition n} (hW : IsColumnWeightString i L W) :
    (∑ k, compositionMonomial (W k)) = isobaric i (compositionMonomial (W 0)) := by
  classical
  have hle : W 0 i.right ≤ W 0 i.left := by have := hW.head; omega
  have hlen : W 0 i.left - W 0 i.right = L := by have := hW.head; omega
  have hs : isobaric i (compositionMonomial (W 0)) =
      ∑ k : Fin (L+1), MvPolynomial.monomial
        (replaceAdjacentExponents (Finsupp.equivFunOnFinite.symm (W 0)) i
          (W 0 i.left-k.val) (W 0 i.right+k.val)) (1:ℤ) := by
    unfold compositionMonomial
    rw [isobaric_monomial i _ (by simpa using hle)]
    simpa only [Finsupp.coe_equivFunOnFinite_symm,hlen] using
      (Fin.sum_univ_eq_sum_range (fun k : ℕ => MvPolynomial.monomial
        (replaceAdjacentExponents (Finsupp.equivFunOnFinite.symm (W 0)) i
          (W 0 i.left-k) (W 0 i.right+k)) (1:ℤ)) (L+1)).symm
  rw [hs]
  apply Finset.sum_congr rfl
  intro k _
  apply congrArg (fun a : Fin n →₀ ℕ => MvPolynomial.monomial a (1:ℤ))
  ext a
  by_cases ha : a = i.left
  · subst a
    simp only [Finsupp.coe_equivFunOnFinite_symm,replaceAdjacentExponents_left]
    have := hW.left k
    omega
  · by_cases hb : a = i.right
    · subst a
      simp only [Finsupp.coe_equivFunOnFinite_symm,replaceAdjacentExponents_right]
      exact hW.right k
    · simp only [Finsupp.coe_equivFunOnFinite_symm,
        replaceAdjacentExponents_of_ne _ _ _ _ _ ha hb]
      exact hW.other k a ha hb

theorem IsColumnWeightString.character_fixed {n L : ℕ} {i : AdjacentPosition n}
    {W : Fin (L+1) → Composition n} (hW : IsColumnWeightString i L W) :
    isobaric i (∑ k, compositionMonomial (W k)) = ∑ k, compositionMonomial (W k) := by
  rw [hW.character,isobaric_idempotent]

end
end Schubert.RS.Representation
