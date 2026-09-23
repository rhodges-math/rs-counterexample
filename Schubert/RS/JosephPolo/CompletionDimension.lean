import Schubert.RS.JosephPolo.PolynomialComparison
import Schubert.RS.PolynomialCompletionCharacterTransfer

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
open scoped BigOperators
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 200000

theorem labelledCharacter_eval_one {n : ℕ} {I : Type*} [Fintype I]
    (a : I → Fin n →₀ ℕ) :
    MvPolynomial.eval (fun _ => (1:ℤ)) (labelledCharacter a) = (Fintype.card I : ℤ) := by
  classical
  simp [labelledCharacter,MvPolynomial.eval_monomial]

theorem PolynomialRootStringBasis.completion_finrank_isobaric {n : ℕ}
    (i : AdjacentPosition n) {S : Submodule ℂ (MatrixPolynomial n)}
    (B : PolynomialRootStringBasis i.left i.right S) (p : RS.Polynomial n)
    (hp : HasTorusCharacter B.sourceTorus p) :
    (Module.finrank ℂ (B.completedModule i.left_ne_right) : ℤ) =
      MvPolynomial.eval (fun _ => (1:ℤ)) (isobaric i p) := by
  have hc : HasTorusCharacter (B.completionTorus i.left_ne_right)
      (labelledCharacter B.completedExponent) := by
    rw [B.completedCharacter_eq]
    exact B.hasCompletedStringCharacter
  rw [(B.completion_character_recursion p hp).unique hc,labelledCharacter_eval_one]
  exact congrArg (fun k : ℕ => (k:ℤ)) (Module.finrank_eq_card_basis (B.completionBasis i.left_ne_right))

theorem PolynomialRootStringBasis.adjacentEvaluation_surjective {n : ℕ}
    (u : Composition n) (i : AdjacentPosition n) (hu : u i.left < u i.right)
    (B : PolynomialRootStringBasis i.left i.right (compositionFlag (swapComposition u i))) :
    Function.Surjective (B.adjacentEvaluation u i hu) := by
  letI := B.completedUpperModule
    (compositionFlag_adjacent_raising_stable (swapComposition u i) i)
    (compositionFlag_radical_stable i (swapComposition u i))
  obtain ⟨c,hc,hmap⟩ := presentation_adjacent_evaluation_scalar u i hu B
  intro y
  obtain ⟨q,hq⟩ := compositionPresentationMap_surjective u (c • y)
  refine ⟨presentationToAdjacentCompletion u i hu B q,?_⟩
  apply smul_right_injective _ hc
  exact (hmap q).symm.trans hq

/-- The independent dimension lower bound suffices for polynomial
injectivity, assuming only the smaller actual character formula. -/
theorem PolynomialRootStringBasis.adjacentEvaluation_bijective_of_dimension_bound {n : ℕ}
    (u : Composition n) (i : AdjacentPosition n) (hu : u i.left < u i.right)
    (B : PolynomialRootStringBasis i.left i.right (compositionFlag (swapComposition u i)))
    (hsmall : HasTorusCharacter (compositionFlagTorus (swapComposition u i))
      (key (swapComposition u i)))
    (hbound : MvPolynomial.eval (fun _ => (1:ℤ)) (key u) ≤
      (Module.finrank ℂ (compositionFlag u) : ℤ)) :
    Function.Bijective (B.adjacentEvaluation u i hu) := by
  have hp : HasTorusCharacter B.sourceTorus (key (swapComposition u i)) := by
    rwa [B.adjacentSourceTorus_eq u i]
  have hc := B.completion_finrank_isobaric i (key (swapComposition u i)) hp
  rw [← key_any_ascent u i hu] at hc
  have hs := B.adjacentEvaluation_surjective u i hu
  have hle := LinearMap.finrank_le_finrank_of_surjective hs
  have hge : Module.finrank ℂ (B.completedModule i.left_ne_right) ≤
      Module.finrank ℂ (compositionFlag u) := by
    have : (Module.finrank ℂ (B.completedModule i.left_ne_right) : ℤ) ≤
        (Module.finrank ℂ (compositionFlag u) : ℤ) := hc.trans_le hbound
    exact_mod_cast this
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (le_antisymm hge hle)).mpr hs,hs⟩

end
end Schubert.RS.Representation
