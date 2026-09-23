import Schubert.RS.JosephPolo.AdjacentTop
import Schubert.RS.AdjacentGeneratorScalar

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
set_option maxHeartbeats 1200000

theorem compositionPresentationMap_stringTop {n : ℕ} (u : Composition n)
    (i : AdjacentPosition n) :
    (compositionPresentationMap u (presentationStringTop u i)).val =
      derivationIter (matrixUnitDerivation i.left i.right) (u i.right-u i.left)
        (compositionFlagGenerator u).val := by
  unfold presentationStringTop
  rw [map_smul, compositionPresentationMap_generator]
  exact polynomialEnveloping_root_pow (adjacentPositiveRoot i) _ _

theorem compositionPresentationMap_stringTop_scalar {n : ℕ} (u : Composition n)
    (i : AdjacentPosition n) (hu : u i.left < u i.right) :
    ∃ c : ℂ, c≠0 ∧ (compositionFlagGenerator (swapComposition u i)).val =
      c • (compositionPresentationMap u (presentationStringTop u i)).val := by
  obtain ⟨c,hc,hg⟩ := compositionFlagGenerator_swap_line u i
  obtain ⟨s,hs,hr⟩ := extremalFlag_swap_iter_weight (compositionShape u) (compositionPermutation u)
    i.left i.right (by simpa only [composition_extremalWeight] using hu)
  rw [composition_extremalWeight] at hr
  change rowRename (Equiv.swap i.left i.right) (compositionFlagGenerator u).val =
    s • derivationIter (matrixUnitDerivation i.left i.right) (u i.right-u i.left)
      (compositionFlagGenerator u).val at hr
  refine ⟨c*s,mul_ne_zero hc hs,?_⟩
  rw [hg, hr, smul_smul, compositionPresentationMap_stringTop]

theorem presentationStringTop_ne_zero {n : ℕ} (u : Composition n)
    (i : AdjacentPosition n) (hu : u i.left < u i.right) :
    presentationStringTop u i ≠ 0 := by
  obtain ⟨c,hc,hg⟩ := compositionPresentationMap_stringTop_scalar u i hu
  intro hz
  rw [hz, map_zero] at hg
  have hg' : (compositionFlagGenerator (swapComposition u i)).val=0 := by simpa using hg
  exact compositionFlagGenerator_ne_zero _ (Subtype.ext hg')

/-- The diagram with the independently defined flag modules commutes up
to a single nonzero scalar, uniformly on all quotient vectors. -/
theorem adjacentPresentationMap_polynomial {n : ℕ} (u : Composition n)
    (i : AdjacentPosition n) (hu : u i.left < u i.right) :
    ∃ c : ℂ, c≠0 ∧ ∀ q : PresentationQuotient (swapComposition u i),
      (compositionPresentationMap (swapComposition u i) q).val =
        c • (compositionPresentationMap u (adjacentPresentationMap u i hu.le q)).val := by
  obtain ⟨c,hc,hg⟩ := compositionPresentationMap_stringTop_scalar u i hu
  refine ⟨c,hc,?_⟩
  intro q
  obtain ⟨a,rfl⟩ := presentation_is_cyclic (swapComposition u i) q
  rw [map_smul, compositionPresentationMap_generator, map_smul,
    adjacentPresentationMap_generator, map_smul]
  change polynomialEnveloping n a (compositionFlagGenerator (swapComposition u i)).val =
    c • polynomialEnveloping n a (compositionPresentationMap u (presentationStringTop u i)).val
  rw [hg, map_smul]

/-- JP for the smaller composition makes this boundary map injective.
This does not assert JP for u or injectivity on the rest of Q_u. -/
theorem adjacentPresentationMap_injective_of_smaller_jp {n : ℕ} (u : Composition n)
    (i : AdjacentPosition n) (hu : u i.left < u i.right)
    (hJP : CompositionFlagJosephPolo (swapComposition u i)) :
    Function.Injective (adjacentPresentationMap u i hu.le) := by
  obtain ⟨c,hc,hdiag⟩ := adjacentPresentationMap_polynomial u i hu
  intro x y hxy
  apply (compositionFlagJosephPolo_iff_injective _).mp hJP
  apply Subtype.ext
  rw [hdiag x, hdiag y, hxy]

end
end Schubert.RS.Representation
