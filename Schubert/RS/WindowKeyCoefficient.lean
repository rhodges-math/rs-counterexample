import Schubert.RS.PresentationCharacter
import Schubert.RS.FullWeightWindow

/-! The key-character window replacement under explicit
representation-theoretic hypotheses. -/

namespace Schubert.RS
noncomputable section
open Representation

variable {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
  [Module (Enveloping n) E] [IsScalarTower ℂ (Enveloping n) E]

/-- The local key-character replacement under the Joseph-Polo, Demazure
character, and PBW hypotheses. The right side is the dimension of a finite
quotient degree piece; its ascent-monomial count is established separately. -/
theorem key_coefficient_eq_linear_window_dimension (u : Composition n)
    (ρ : DiagonalTorus n →* Module.End ℂ E) (ξ : E)
    (hJP : HasJosephPoloPresentation u ρ ξ) (hDCF : HasDemazureCharacter u ρ)
    (hpbw : HasOrderedPBWBasis n) (β d : RootDegree n) (hd : d ≤ β)
    (hβ : ∀ r : PositiveRoot n, u r.val.1 < u r.val.2 →
      ¬ jpExponent u r • rootDegree r.val.1 r.val.2 ≤ β) :
    (toLaurent (key u)).coeff (weightOfRootDegree u d) =
      (Module.finrank ℂ (linearDegreePiece u hpbw d) : ℤ) := by
  rw [← jpWeight_coefficient u ρ ξ hJP hDCF (weightOfRootDegree u d),
    ← jpDegreePiece_eq_fullWeightSpace u hpbw d,
    ← windowDegree_finrank u hpbw β d hd hβ]

end
end Schubert.RS
