import Schubert.RS.EnvelopingOrbit
import Schubert.RS.ParabolicCyclicSpan
import Schubert.RS.UpperRadicalGenerators
import Schubert.RS.Representation.ParabolicUpperRepresentation

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

theorem parabolicUpperLie_adjacent (x : X) :
    parabolicUpperLie i X (rootBasis n (adjacentPositiveRoot i)) x=
      ⁅sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right),x⁆ := by
  rw [parabolicUpperLie_apply,upperSimpleCoefficient_adjacent,upperRadicalPart_adjacent,
    one_smul,zero_lie,add_zero]

variable (z : X)

theorem parabolicOrbit_raising {x : X}
    (hx : x∈envelopingOrbit (parabolicUpperEnveloping i X) z) :
    ⁅sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right),x⁆∈
      envelopingOrbit (parabolicUpperEnveloping i X) z := by
  have hh := envelopingOrbit_stable (parabolicUpperEnveloping i X) z
    (UniversalEnvelopingAlgebra.ι ℂ (rootBasis n (adjacentPositiveRoot i))) hx
  rw [parabolicUpperEnveloping_ι,parabolicUpperLie_adjacent] at hh
  exact hh

theorem parabolicOrbit_radical (r : radicalEndLie i) {x : X}
    (hx : x∈envelopingOrbit (parabolicUpperEnveloping i X) z) :
    ⁅r,x⁆∈envelopingOrbit (parabolicUpperEnveloping i X) z := by
  obtain ⟨A,hA⟩ := upperRadicalPart_surjective i r
  have hh := envelopingOrbit_stable (parabolicUpperEnveloping i X) z
    (UniversalEnvelopingAlgebra.ι ℂ A) hx
  rw [parabolicUpperEnveloping_ι,parabolicUpperLie_apply,hA] at hh
  have he := (envelopingOrbit (parabolicUpperEnveloping i X) z).smul_mem
    (upperSimpleCoefficient i A) (parabolicOrbit_raising i X z hx)
  have hd := (envelopingOrbit (parabolicUpperEnveloping i X) z).sub_mem hh he
  simpa only [add_sub_cancel_left] using hd

/-- Raising and radical generation agrees exactly with the orbit under
the genuine upper enveloping algebra; no PBW basis is invoked. -/
theorem parabolicOrbit_eq_cyclicSpan :
    envelopingOrbit (parabolicUpperEnveloping i X) z=
      raisingRadicalCyclicSpan (polynomialSl2Triple i.left i.right i.left_ne_right)
        (R := radicalEndLie i) z := by
  apply le_antisymm
  · apply envelopingOrbit_le
    · exact operatorCyclicSpan_generator _ z
    · intro A x hx
      rw [parabolicUpperEnveloping_ι,parabolicUpperLie_apply]
      apply (raisingRadicalCyclicSpan _ (R := radicalEndLie i) z).add_mem
      · apply (raisingRadicalCyclicSpan _ (R := radicalEndLie i) z).smul_mem
        exact operatorCyclicSpan_stable
          (raisingRadicalOperators (polynomialSl2Triple i.left i.right i.left_ne_right)
            (R := radicalEndLie i) (X := X)) z (.inl ()) hx
      · exact operatorCyclicSpan_stable _ z (.inr (upperRadicalPart i A)) hx
  · apply operatorCyclicSpan_le
    · exact envelopingOrbit_generator _ z
    · intro j x hx
      cases j with
      | inl u => exact parabolicOrbit_raising i X z hx
      | inr r => exact parabolicOrbit_radical i X z r hx

end
end Schubert.RS.Representation
