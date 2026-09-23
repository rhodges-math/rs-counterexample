import Schubert.RS.JosephPolo.LoweringCartan

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1600000

theorem loweringEnveloping_cartan {n : ℕ} (i : AdjacentPosition n) (w : ℂ) :
    cartanEnveloping (adjacentCartanDiagonal i)*loweringEnveloping i w -
      loweringEnveloping i w*cartanEnveloping (adjacentCartanDiagonal i) =
      (-2 : ℂ) • loweringEnveloping i w := by
  let D := cartanEnveloping (adjacentCartanDiagonal i)
  let F := loweringEnveloping i w
  let δ := loweringEnvelopingCocycle i w
  let K : Module.End ℂ (Enveloping n) := D*F-F*D+(2 : ℂ) • F
  have hF (A : upperNilpotent n) (a : Enveloping n) :
      F (UniversalEnvelopingAlgebra.ι ℂ A*a) = UniversalEnvelopingAlgebra.ι ℂ A*F a+δ A a :=
    envelopingCocycleOperator_generator_mul _ _ _ _
  have hD (A : upperNilpotent n) (a : Enveloping n) :
      D (UniversalEnvelopingAlgebra.ι ℂ A*a) = UniversalEnvelopingAlgebra.ι ℂ A*D a+
        UniversalEnvelopingAlgebra.ι ℂ (cartanUpper (adjacentCartanDiagonal i) A)*a :=
    cartanEnveloping_generator_mul _ _ _
  have hδ (A : upperNilpotent n) (a : Enveloping n) :
      δ (cartanUpper (adjacentCartanDiagonal i) A) a =
        D (δ A a)-δ A (D a)+(2 : ℂ) • δ A a :=
    congrArg (fun T : Module.End ℂ (Enveloping n) => T a) (loweringEnvelopingCocycle_cartan i w A)
  have hK (A : upperNilpotent n) (a : Enveloping n) :
      K (UniversalEnvelopingAlgebra.ι ℂ A*a) = UniversalEnvelopingAlgebra.ι ℂ A*K a := by
    change D (F (UniversalEnvelopingAlgebra.ι ℂ A*a)) -
      F (D (UniversalEnvelopingAlgebra.ι ℂ A*a)) + (2 : ℂ) • F (UniversalEnvelopingAlgebra.ι ℂ A*a) =
      UniversalEnvelopingAlgebra.ι ℂ A*(D (F a)-F (D a)+(2 : ℂ) • F a)
    simp only [hF, hD, map_add, hδ, smul_add, mul_add, mul_sub, mul_smul_comm]
    abel
  have hKone : K 1=0 := by
    change D (F 1)-F (D 1)+(2 : ℂ) • F 1=0
    have hFone : F 1=0 := loweringEnveloping_one i w
    have hDone : D 1=0 := cartanEnveloping_one _
    rw [hFone, hDone, map_zero, map_zero, sub_zero, smul_zero, add_zero]
  have hzero : K=0 := by
    apply LinearMap.ext
    intro a
    change K a=0
    have ht := enveloping_intertwines (regularEnvelopingAction n) (regularEnvelopingAction n)
      K (fun A b => hK A b) a 1
    change K (a*1)=a*K 1 at ht
    simpa only [mul_one, hKone, mul_zero] using ht
  change D*F-F*D+(2 : ℂ) • F=0 at hzero
  have he : D*F-F*D = -((2 : ℂ) • F) := eq_neg_of_add_eq_zero_left hzero
  simpa only [neg_smul] using he

theorem shiftedCartanEnveloping_lowering {n : ℕ} (i : AdjacentPosition n) (w : ℂ) :
    (cartanEnveloping (adjacentCartanDiagonal i)+w • 1)*loweringEnveloping i w -
      loweringEnveloping i w*(cartanEnveloping (adjacentCartanDiagonal i)+w • 1) =
      (-2 : ℂ) • loweringEnveloping i w := by
  rw [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  have h := loweringEnveloping_cartan i w
  convert h using 1 <;> abel

end
end Schubert.RS.Representation
