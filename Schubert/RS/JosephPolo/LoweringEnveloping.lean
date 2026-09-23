import Schubert.RS.JosephPolo.LoweringLie
import Schubert.RS.JosephPolo.CartanEnveloping

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1600000

def loweringEnvelopingCocycle {n : ℕ} (i : AdjacentPosition n) (w : ℂ) :
    upperNilpotent n →ₗ[ℂ] Module.End ℂ (Enveloping n) :=
  (regularEnvelopingAction n).toLinearMap.comp
    ((UniversalEnvelopingAlgebra.ι ℂ).toLinearMap.comp (loweringUpper i)) -
      (upperSimpleCoefficient i).smulRight (cartanEnveloping (adjacentCartanDiagonal i)+w • 1)

theorem loweringEnvelopingCocycle_apply {n : ℕ} (i : AdjacentPosition n) (w : ℂ)
    (A : upperNilpotent n) :
    loweringEnvelopingCocycle i w A =
      regularEnvelopingAction n (UniversalEnvelopingAlgebra.ι ℂ (loweringUpper i A)) -
      upperSimpleCoefficient i A • (cartanEnveloping (adjacentCartanDiagonal i)+w • 1) := rfl

theorem loweringEnvelopingCocycle_lie {n : ℕ} (i : AdjacentPosition n) (w : ℂ)
    (A B : upperNilpotent n) :
    loweringEnvelopingCocycle i w ⁅A,B⁆ =
      regularEnvelopingAction n (UniversalEnvelopingAlgebra.ι ℂ A) * loweringEnvelopingCocycle i w B +
        loweringEnvelopingCocycle i w A * regularEnvelopingAction n (UniversalEnvelopingAlgebra.ι ℂ B) -
        regularEnvelopingAction n (UniversalEnvelopingAlgebra.ι ℂ B) * loweringEnvelopingCocycle i w A -
        loweringEnvelopingCocycle i w B * regularEnvelopingAction n (UniversalEnvelopingAlgebra.ι ℂ A) := by
  let ρ := regularEnvelopingAction n
  have he (C D : upperNilpotent n) : ρ (UniversalEnvelopingAlgebra.ι ℂ ⁅C,D⁆) =
      ρ (UniversalEnvelopingAlgebra.ι ℂ C) * ρ (UniversalEnvelopingAlgebra.ι ℂ D) -
        ρ (UniversalEnvelopingAlgebra.ι ℂ D) * ρ (UniversalEnvelopingAlgebra.ι ℂ C) := by
    rw [LieHom.map_lie]
    change ρ (_*_ - _*_) = _
    rw [map_sub, map_mul, map_mul]
  have hr := congrArg (fun C : upperNilpotent n => ρ (UniversalEnvelopingAlgebra.ι ℂ C))
    (loweringUpper_lie i A B)
  simp only [map_add, map_sub, map_smul, he] at hr
  rw [loweringEnvelopingCocycle_apply, upperSimpleCoefficient_bracket, zero_smul, sub_zero]
  change ρ (UniversalEnvelopingAlgebra.ι ℂ (loweringUpper i ⁅A,B⁆)) = _
  rw [hr]
  change _ = _
  rw [show ρ (UniversalEnvelopingAlgebra.ι ℂ (cartanUpper (adjacentCartanDiagonal i) B)) =
      (cartanEnveloping (adjacentCartanDiagonal i)+w • 1) * ρ (UniversalEnvelopingAlgebra.ι ℂ B) -
      ρ (UniversalEnvelopingAlgebra.ι ℂ B) * (cartanEnveloping (adjacentCartanDiagonal i)+w • 1)
      from (shiftedCartanEnveloping_commutator _ w B).symm]
  rw [show ρ (UniversalEnvelopingAlgebra.ι ℂ (cartanUpper (adjacentCartanDiagonal i) A)) =
      (cartanEnveloping (adjacentCartanDiagonal i)+w • 1) * ρ (UniversalEnvelopingAlgebra.ι ℂ A) -
      ρ (UniversalEnvelopingAlgebra.ι ℂ A) * (cartanEnveloping (adjacentCartanDiagonal i)+w • 1)
      from (shiftedCartanEnveloping_commutator _ w A).symm]
  simp only [loweringEnvelopingCocycle_apply, mul_sub, sub_mul,
    smul_mul_assoc, mul_smul_comm, smul_sub, mul_add, add_mul]
  dsimp only [ρ]
  module

/-- The lowering operator on U(n+), with the cyclic generator assigned
Cartan weight w. This is an actual linear operator, not an existence input. -/
def loweringEnveloping {n : ℕ} (i : AdjacentPosition n) (w : ℂ) : Module.End ℂ (Enveloping n) :=
  envelopingCocycleOperator (loweringEnvelopingCocycle i w) (loweringEnvelopingCocycle_lie i w)

theorem loweringEnveloping_one {n : ℕ} (i : AdjacentPosition n) (w : ℂ) :
    loweringEnveloping i w 1=0 := envelopingCocycleOperator_one _ _

theorem loweringEnveloping_generator_mul {n : ℕ} (i : AdjacentPosition n) (w : ℂ)
    (A : upperNilpotent n) (a : Enveloping n) :
    loweringEnveloping i w (UniversalEnvelopingAlgebra.ι ℂ A*a) =
      UniversalEnvelopingAlgebra.ι ℂ A*loweringEnveloping i w a +
      (UniversalEnvelopingAlgebra.ι ℂ (loweringUpper i A)*a -
        upperSimpleCoefficient i A • (cartanEnveloping (adjacentCartanDiagonal i) a+w • a)) :=
  envelopingCocycleOperator_generator_mul _ _ _ _

end
end Schubert.RS.Representation
