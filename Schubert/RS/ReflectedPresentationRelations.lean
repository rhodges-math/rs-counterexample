import Schubert.RS.PresentationRigidity
import Schubert.RS.WeylDenominator

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation

/-- A simple reflection preserves every positive root other than itself. -/
def adjacentReflectedRoot {n : ℕ} (i : AdjacentPosition n) (r : PositiveRoot n)
    (hr : r.val ≠ (i.left,i.right)) : PositiveRoot n :=
  ⟨(adjacentTransposition i r.val.1,adjacentTransposition i r.val.2),
    ((adjacent_preserves_other_positive_pairs i r.val.1 r.val.2).mpr ⟨r.property,hr⟩).1⟩

theorem jpExponent_reflected {n : ℕ} (v : Composition n) (i : AdjacentPosition n)
    (r : PositiveRoot n) (hr : r.val ≠ (i.left,i.right)) :
    jpExponent (swapComposition v i) r = jpExponent v (adjacentReflectedRoot i r hr) := rfl

variable {n : ℕ} {X : Type*} [AddCommGroup X] [Module ℂ X]
  [Module (Enveloping n) X] [IsScalarTower ℂ (Enveloping n) X]

/-- Conjugation of a root action transports every power, including its
normalizing scalar. No nonzero scalar assumption is needed to transport zero. -/
theorem root_power_transport (a b : Enveloping n) (τ : X →ₗ[ℂ] X) (c : ℂ)
    (hτ : ∀ x : X, a • τ x = c • τ (b • x)) (k : ℕ) (x : X) :
    a^k • τ x = c^k • τ (b^k • x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ',mul_smul,ih,smul_comm a (c^k),hτ,smul_smul,pow_succ]
    rw [pow_succ',mul_smul]
    simp only [mul_smul]

/-- The non-simple JP relations for a reflected cyclic vector follow just
from Weyl conjugation. The remaining simple-root relation is the ordinary
finite sl₂ string endpoint, stated separately here for the completion route. -/
theorem reflected_vector_jp_relations (v : Composition n) (i : AdjacentPosition n)
    (ξ : X) (τ : X →ₗ[ℂ] X)
    (hξ : ∀ r : PositiveRoot n, (rootOperator r ^ jpExponent v r) • ξ = 0)
    (c : PositiveRoot n → ℂ)
    (hτ : ∀ (r : PositiveRoot n) (hr : r.val ≠ (i.left,i.right)) (x : X),
      rootOperator r • τ x = c r • τ (rootOperator (adjacentReflectedRoot i r hr) • x))
    (hsimple : (rootOperator ⟨(i.left,i.right),i.left_lt_right⟩ ^
      jpExponent (swapComposition v i) ⟨(i.left,i.right),i.left_lt_right⟩) • τ ξ = 0) :
    ∀ r : PositiveRoot n, (rootOperator r ^ jpExponent (swapComposition v i) r) • τ ξ = 0 := by
  intro r
  by_cases hr : r.val=(i.left,i.right)
  · have he : r=⟨(i.left,i.right),i.left_lt_right⟩ := Subtype.ext hr
    subst r
    exact hsimple
  · rw [jpExponent_reflected v i r hr,
      root_power_transport _ _ τ (c r) (hτ r hr),hξ,map_zero,smul_zero]

/-- A cyclic reflected module satisfying the Joseph-Polo relations is
isomorphic to the flag module under the stated presentation hypothesis. -/
theorem reflected_completion_bijective (v : Composition n) (i : AdjacentPosition n)
    (hJP : CompositionFlagJosephPolo (swapComposition v i))
    (ξ : X) (τ : X →ₗ[ℂ] X)
    (hξ : ∀ r : PositiveRoot n, (rootOperator r ^ jpExponent v r) • ξ = 0)
    (c : PositiveRoot n → ℂ)
    (hτ : ∀ (r : PositiveRoot n) (hr : r.val ≠ (i.left,i.right)) (x : X),
      rootOperator r • τ x = c r • τ (rootOperator (adjacentReflectedRoot i r hr) • x))
    (hsimple : (rootOperator ⟨(i.left,i.right),i.left_lt_right⟩ ^
      jpExponent (swapComposition v i) ⟨(i.left,i.right),i.left_lt_right⟩) • τ ξ = 0)
    (hcyc : ∀ x : X, ∃ a : Enveloping n, a • τ ξ = x)
    (f : X →ₗ[Enveloping n] compositionFlag (swapComposition v i))
    (hf : f (τ ξ) = compositionFlagGenerator (swapComposition v i)) :
    Function.Bijective f :=
  compositionPresentation_rigidity _ hJP (τ ξ)
    (reflected_vector_jp_relations v i ξ τ hξ c hτ hsimple) hcyc f hf

end
end Schubert.RS.Representation
