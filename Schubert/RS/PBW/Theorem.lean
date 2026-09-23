import Schubert.RS.PBW.Independence
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! PBW for the actual strictly upper triangular complex matrix Lie algebra,
for every rank and every ordering of its positive matrix units. -/
namespace Schubert.RS.Representation
noncomputable section

def orderedRootBasis {n : ℕ} (order : RootOrdering n) :
    Module.Basis (PositiveRoot n → ℕ) ℂ (Enveloping n) :=
  Module.Basis.mk (orderedRootMonomial_linearIndependent order)
    (by rw [orderedRootMonomial_span_eq_top])

@[simp] theorem orderedRootBasis_apply {n : ℕ} (order : RootOrdering n)
    (powers : PositiveRoot n → ℕ) :
    orderedRootBasis order powers = orderedRootMonomial order powers := by
  simp [orderedRootBasis]

/-- The ordered-root PBW basis theorem for the enveloping algebra. -/
theorem orderedPBWBasis_exists (n : ℕ) : HasOrderedPBWBasis n := by
  intro order
  exact ⟨orderedRootBasis order, orderedRootBasis_apply order⟩

end
end Schubert.RS.Representation
