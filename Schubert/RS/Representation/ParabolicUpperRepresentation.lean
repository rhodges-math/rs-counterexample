import Schubert.RS.Representation.UpperRadicalDecomposition
import Schubert.RS.Representation.CyclicGeneration

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ} (i : AdjacentPosition n) (X : Type*) [AddCommGroup X] [Module ℂ X]
  [LieRingModule ((polynomialSl2Triple i.left i.right i.left_ne_right).toLieSubalgebra ℂ) X]
  [LieModule ℂ ((polynomialSl2Triple i.left i.right i.left_ne_right).toLieSubalgebra ℂ) X]
  [LieRingModule (radicalEndLie i) X] [LieModule ℂ (radicalEndLie i) X]
  [IsLieTower ((polynomialSl2Triple i.left i.right i.left_ne_right).toLieSubalgebra ℂ)
    (radicalEndLie i) X]

def parabolicRaisingEnd : Module.End ℂ X :=
  LieModule.toEnd ℂ _ X
    (sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right))

theorem radical_toEnd_raising (r : radicalEndLie i) :
    LieModule.toEnd ℂ (radicalEndLie i) X
      ⁅sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right),r⁆ =
    ⁅parabolicRaisingEnd i X,LieModule.toEnd ℂ (radicalEndLie i) X r⁆ := by
  apply LinearMap.ext
  intro x
  change ⁅⁅sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right),r⁆,x⁆ =
    ⁅sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right),⁅r,x⁆⁆ -
      ⁅r,⁅sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right),x⁆⁆
  rw [IsLieTower.leibniz_lie]
  abel

/-- The actual upper-nilpotent representation obtained from a compatible
rank-one and radical action. -/
def parabolicUpperLie : upperNilpotent n →ₗ⁅ℂ⁆ Module.End ℂ X where
  toLinearMap := (upperSimpleCoefficient i).smulRight (parabolicRaisingEnd i X) +
    (LieModule.toEnd ℂ (radicalEndLie i) X).toLinearMap.comp (upperRadicalPart i)
  map_lie' {A B} := by
    change upperSimpleCoefficient i ⁅A,B⁆ • parabolicRaisingEnd i X +
      LieModule.toEnd ℂ (radicalEndLie i) X (upperRadicalPart i ⁅A,B⁆) =
      ⁅upperSimpleCoefficient i A • parabolicRaisingEnd i X +
          LieModule.toEnd ℂ (radicalEndLie i) X (upperRadicalPart i A),
        upperSimpleCoefficient i B • parabolicRaisingEnd i X +
          LieModule.toEnd ℂ (radicalEndLie i) X (upperRadicalPart i B)⁆
    rw [upperSimpleCoefficient_bracket,zero_smul,zero_add,upperRadicalPart_bracket]
    simp only [map_add,map_sub,map_smul,LieHom.map_lie,radical_toEnd_raising]
    simp only [Ring.lie_def,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,smul_sub]
    module

theorem parabolicUpperLie_apply (A : upperNilpotent n) (x : X) :
    parabolicUpperLie i X A x = upperSimpleCoefficient i A •
      ⁅sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right),x⁆ +
      ⁅upperRadicalPart i A,x⁆ := rfl

/-- The resulting actual enveloping-algebra action. -/
def parabolicUpperEnveloping : Enveloping n →ₐ[ℂ] Module.End ℂ X :=
  UniversalEnvelopingAlgebra.lift ℂ (parabolicUpperLie i X)

theorem parabolicUpperEnveloping_ι (A : upperNilpotent n) :
    parabolicUpperEnveloping i X (UniversalEnvelopingAlgebra.ι ℂ A) =
      parabolicUpperLie i X A :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℂ _ A

@[instance_reducible] def parabolicUpperModule : Module (Enveloping n) X :=
  Module.compHom X (parabolicUpperEnveloping i X).toRingHom

theorem parabolicUpperTower :
    letI := parabolicUpperModule i X
    IsScalarTower ℂ (Enveloping n) X := by
  letI := parabolicUpperModule i X
  exact ⟨fun c a x => by
    change parabolicUpperEnveloping i X (c • a) x = c • parabolicUpperEnveloping i X a x
    rw [map_smul]
    rfl⟩

end
end Schubert.RS.Representation
