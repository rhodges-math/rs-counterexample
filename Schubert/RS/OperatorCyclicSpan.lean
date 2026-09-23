import Schubert.RS.RankOneCompletionGeneration
import Schubert.RS.Representation.ParabolicRadical

namespace Schubert.RS.Representation
noncomputable section

variable {I X : Type*} [AddCommGroup X] [Module ℂ X]
  (D : I → Module.End ℂ X) (z : X)

/-- The smallest linear subspace containing z and stable under the specified
operators. This definition carries no finite-dimensionality assumption. -/
def operatorCyclicSpan : Submodule ℂ X :=
  operatorCyclic z D

theorem operatorCyclicSpan_le (Y : Submodule ℂ X) (hz : z∈Y)
    (hY : ∀ i x, x∈Y → D i x∈Y) : operatorCyclicSpan D z≤Y :=
  operatorCyclic_le z D Y hz hY

theorem operatorCyclicSpan_generator : z∈operatorCyclicSpan D z :=
  operatorCyclic_seed z D

theorem operatorCyclicSpan_stable (i : I) {x : X} (hx : x∈operatorCyclicSpan D z) :
    D i x∈operatorCyclicSpan D z := operatorCyclic_stable z D i hx

/-- Stability under an extra operator follows from its value at the cyclic
generator and its commutators with the generating operators. -/
theorem operatorCyclicSpan_extra (A : Module.End ℂ X)
    (hz : A z∈operatorCyclicSpan D z)
    (hcomm : ∀ i x, x∈operatorCyclicSpan D z → (A (D i x)-D i (A x))∈operatorCyclicSpan D z)
    {x : X} (hx : x∈operatorCyclicSpan D z) : A x∈operatorCyclicSpan D z :=
  cyclic_core_stability (operatorCyclicSpan D z) z D A
    (operatorCyclicSpan_le D z) (operatorCyclicSpan_generator D z)
    (fun i x hx => operatorCyclicSpan_stable D z i hx) hz hcomm hx

end
end Schubert.RS.Representation
