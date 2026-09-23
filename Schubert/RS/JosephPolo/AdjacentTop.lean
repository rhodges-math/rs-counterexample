import Schubert.RS.JosephPolo.RootPairRelations
import Schubert.RS.PresentationRigidity

/-! The highest end of a simple-root string in the universal quotient
satisfies the full presentation for the swapped composition. This result
is proved from root commutators, with no JP input. -/

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
set_option maxHeartbeats 1200000

def presentationStringTop {n : ℕ} (u : Composition n) (i : AdjacentPosition n) :
    PresentationQuotient u :=
  rootOperator (adjacentPositiveRoot i) ^ (u i.right-u i.left) • presentationGenerator u

theorem presentationStringTop_jp {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (hu : u i.left ≤ u i.right) (r : PositiveRoot n) :
    rootOperator r ^ jpExponent (swapComposition u i) r • presentationStringTop u i = 0 := by
  rcases r with ⟨⟨a,b⟩,hab⟩
  by_cases hbl : b=i.left
  · subst b
    have hal : a≠i.left := ne_of_lt hab
    have har : a≠i.right := ne_of_lt (hab.trans i.left_lt_right)
    change rootOperator ⟨(a,i.left),hab⟩ ^
      (swapComposition u i i.left-swapComposition u i a+1) • presentationStringTop u i=0
    rw [swapComposition_left, swapComposition_other u i a hal har]
    exact (jp_incoming_string_bounds u i hu a hab).1
  by_cases hbr : b=i.right
  · subst b
    by_cases hal : a=i.left
    · subst a
      change rootOperator (adjacentPositiveRoot i) ^
        (swapComposition u i i.right-swapComposition u i i.left+1) •
        (rootOperator (adjacentPositiveRoot i)^(u i.right-u i.left) • presentationGenerator u)=0
      rw [swapComposition_right, swapComposition_left, Nat.sub_eq_zero_of_le hu,
        zero_add, pow_one, ← mul_smul, ← pow_succ']
      exact jp_relation_kills_generator u (adjacentPositiveRoot i)
    · have ha : a < i.left := by
        have hv := i.right_val
        have hne : a.val≠i.left.val := fun h => hal (Fin.ext h)
        change a.val < i.left.val
        change a.val < i.right.val at hab
        omega
      have har : a≠i.right := ne_of_lt hab
      change rootOperator ⟨(a,i.right),hab⟩ ^
        (swapComposition u i i.right-swapComposition u i a+1) • presentationStringTop u i=0
      rw [swapComposition_right, swapComposition_other u i a hal har]
      exact (jp_incoming_string_bounds u i hu a ha).2
  by_cases hal : a=i.left
  · subst a
    have hb : i.right < b := by
      have hv := i.right_val
      have hne : b.val≠i.right.val := fun h => hbr (Fin.ext h)
      change i.right.val < b.val
      change i.left.val < b.val at hab
      omega
    change rootOperator ⟨(i.left,b),hab⟩ ^
      (swapComposition u i b-swapComposition u i i.left+1) • presentationStringTop u i=0
    rw [swapComposition_other u i b hbl hbr, swapComposition_left]
    exact (jp_outgoing_string_bounds u i hu b hb).2
  by_cases har : a=i.right
  · subst a
    change rootOperator ⟨(i.right,b),hab⟩ ^
      (swapComposition u i b-swapComposition u i i.right+1) • presentationStringTop u i=0
    rw [swapComposition_other u i b hbl hbr, swapComposition_right]
    exact (jp_outgoing_string_bounds u i hu b hab).1
  · have hc : Commute (rootOperator ⟨(a,b),hab⟩) (rootOperator (adjacentPositiveRoot i)) :=
      rootOperator_commute _ _ hbl (Ne.symm har)
    have he : jpExponent (swapComposition u i) ⟨(a,b),hab⟩ = jpExponent u ⟨(a,b),hab⟩ := by
      simp only [jpExponent, swapComposition_other u i b hbl hbr,
        swapComposition_other u i a hal har]
    rw [he]
    unfold presentationStringTop
    rw [← mul_smul, ((hc.pow_left _).pow_right _).eq, mul_smul,
      jp_relation_kills_generator u ⟨(a,b),hab⟩, smul_zero]

/-- The induction's canonical upper-equivariant map. No injectivity
assertion is folded into its construction. -/
def adjacentPresentationMap {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (hu : u i.left ≤ u i.right) :
    PresentationQuotient (swapComposition u i) →ₗ[Enveloping n] PresentationQuotient u :=
  presentationLift (swapComposition u i) (presentationStringTop u i)
    (presentationStringTop_jp u i hu)

theorem adjacentPresentationMap_generator {n : ℕ} (u : Composition n)
    (i : AdjacentPosition n) (hu : u i.left ≤ u i.right) :
    adjacentPresentationMap u i hu (presentationGenerator (swapComposition u i)) =
      presentationStringTop u i :=
  presentationLift_generator _ _ _

end
end Schubert.RS.Representation
