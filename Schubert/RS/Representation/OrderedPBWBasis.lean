import Schubert.RS.Representation.RootBasis
import Schubert.RS.Representation.Presentation

namespace Schubert.RS.Representation

noncomputable section

/-- A total ordering of the concrete positive-root basis, as an enumeration. -/
structure RootOrdering (n : ℕ) where
  roots : List (PositiveRoot n)
  nodup : roots.Nodup
  complete : ∀ r, r ∈ roots

/-- The ordering type is inhabited; HasOrderedPBWBasis is not vacuous. -/
def defaultRootOrdering (n : ℕ) : RootOrdering n := by
  classical
  exact ⟨Finset.univ.toList, Finset.nodup_toList _, by simp⟩

/-- Products are taken in the specified order in the actual noncommutative UEA. -/
def orderedRootMonomial {n : ℕ} (order : RootOrdering n)
    (powers : PositiveRoot n → ℕ) : Enveloping n :=
  (order.roots.map fun r =>
    (UniversalEnvelopingAlgebra.ι ℂ (rootBasis n r)) ^ powers r).prod

theorem orderedRootMonomial_eq {n : ℕ} (order : RootOrdering n)
    (powers : PositiveRoot n → ℕ) :
    orderedRootMonomial order powers =
      (order.roots.map fun r => rootOperator r ^ powers r).prod := by
  simp only [orderedRootMonomial, rootBasis_apply, rootOperator]

/-- The ordered-root monomial basis property for the enveloping algebra.
A proof of this proposition is provided by PBW.Theorem. -/
def HasOrderedPBWBasis (n : ℕ) : Prop :=
  ∀ order : RootOrdering n,
    ∃ b : Module.Basis (PositiveRoot n → ℕ) ℂ (Enveloping n),
      ∀ powers, b powers = orderedRootMonomial order powers

end
end Schubert.RS.Representation
