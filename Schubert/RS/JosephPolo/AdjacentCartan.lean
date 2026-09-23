import Schubert.RS.JosephPolo.CartanCovariance

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
set_option maxHeartbeats 400000

theorem presentationCartan_stringTop {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (hu : u i.left ≤ u i.right) :
    presentationCartan u i (presentationStringTop u i) =
      (((swapComposition u i) i.left : ℂ)-((swapComposition u i) i.right : ℂ)) •
        presentationStringTop u i := by
  have he : adjacentCartanDiagonal i (adjacentPositiveRoot i).val.1-
      adjacentCartanDiagonal i (adjacentPositiveRoot i).val.2=2 := adjacentCartan_simple_weight i
  unfold presentationStringTop
  rw [presentationCartan_smul, cartanEnveloping_root_pow, he, presentationCartan_generator,
    smul_assoc, smul_comm (rootOperator (adjacentPositiveRoot i)^(u i.right-u i.left))
      ((u i.left : ℂ)-(u i.right : ℂ))]
  simp only [swapComposition_left, swapComposition_right, Nat.cast_sub hu]
  rw [← add_smul]
  congr 1
  ring

theorem adjacentPresentationMap_cartan {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (hu : u i.left ≤ u i.right) (x : PresentationQuotient (swapComposition u i)) :
    adjacentPresentationMap u i hu (presentationCartan (swapComposition u i) i x) =
      presentationCartan u i (adjacentPresentationMap u i hu x) := by
  obtain ⟨a,rfl⟩ := presentation_is_cyclic (swapComposition u i) x
  let g := adjacentPresentationMap u i hu
  have hc (c : ℂ) (q : PresentationQuotient (swapComposition u i)) : g (c • q)=c • g q :=
    (g.restrictScalars ℂ).map_smul c q
  change g (presentationCartan (swapComposition u i) i
    (a • presentationGenerator (swapComposition u i))) = presentationCartan u i
      (g (a • presentationGenerator (swapComposition u i)))
  rw [presentationCartan_smul, map_add, map_smul, map_smul, map_smul,
    presentationCartan_generator, hc]
  have hg : g (presentationGenerator (swapComposition u i))=presentationStringTop u i :=
    adjacentPresentationMap_generator u i hu
  rw [hg, presentationCartan_smul, presentationCartan_stringTop u i hu]

end
end Schubert.RS.Representation
