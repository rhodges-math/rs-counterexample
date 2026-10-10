import RSCounterexample.Demazure.ReflectedPresentationRelations

/-!
# Joseph–Polo relations at reflected endpoints

Let `ξ` satisfy the Joseph–Polo relations of `swapComposition u i`, and let `τ` transport each
non-simple root operator to its reflection up to a scalar. If `τ ξ = s • η` with `s ≠ 0` and `η`
satisfies the relation of the simple root of `i` for `u`, then `η` satisfies all Joseph–Polo
relations of `u` (`reflected_endpoint_josephPolo_relations`).
-/

open Schubert

namespace Demazure.FlagModule
noncomputable section
open FinPermutation

variable {n : ℕ} {X : Type*} [AddCommGroup X] [Module ℂ X]
  [Module (Enveloping n) X] [IsScalarTower ℂ (Enveloping n) X]

/-- Transported root powers descend from a Weyl-reflected vector to any
explicitly nonzero scalar normalization of its lowest endpoint. -/
theorem reflected_endpoint_josephPolo_relations (u : Composition n) (i : AdjacentPosition n)
    (ξ η : X) (τ : X →ₗ[ℂ] X)
    (hξ : ∀ r : PositiveRoot n, (rootOperator r^josephPoloExponent (swapComposition u i) r) • ξ=0)
    (c : PositiveRoot n → ℂ)
    (hτ : ∀ (r : PositiveRoot n) (hr : r.val≠(i.left,i.right)) (x : X),
      rootOperator r • τ x=c r • τ (rootOperator (adjacentReflectedRoot i r hr) • x))
    (s : ℂ) (hs : s≠0) (hη : τ ξ=s • η)
    (hsimple : (rootOperator ⟨(i.left,i.right),i.left_lt_right⟩^
      josephPoloExponent u ⟨(i.left,i.right),i.left_lt_right⟩) • η=0) :
    ∀ r : PositiveRoot n, (rootOperator r^josephPoloExponent u r) • η=0 := by
  have hsimple' : (rootOperator ⟨(i.left,i.right),i.left_lt_right⟩^
      josephPoloExponent (swapComposition (swapComposition u i) i)
          ⟨(i.left,i.right),i.left_lt_right⟩) • τ ξ=0 := by
    rw [swapComposition_involutive,hη,smul_comm,hsimple,smul_zero]
  have hh := reflected_vector_josephPolo_relations (swapComposition u i) i ξ τ hξ c hτ hsimple'
  rw [swapComposition_involutive] at hh
  intro r
  have hr := hh r
  rw [hη,smul_comm] at hr
  exact (smul_eq_zero.mp hr).resolve_left hs

end
end Demazure.FlagModule
