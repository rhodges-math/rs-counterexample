import Schubert.RS.ParabolicCyclicOrbit
import Schubert.RS.Sl2EndpointGeneration

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance 100] LieRing.ofAssociativeRing
universe u

variable {n : ℕ} (i : AdjacentPosition n) {X : Type u} [AddCommGroup X] [Module ℂ X]
  [LieRingModule ((polynomialSl2Triple i.left i.right i.left_ne_right).toLieSubalgebra ℂ) X]
  [LieModule ℂ ((polynomialSl2Triple i.left i.right i.left_ne_right).toLieSubalgebra ℂ) X]
  [LieRingModule (radicalEndLie i) X] [LieModule ℂ (radicalEndLie i) X]
  [IsLieTower ((polynomialSl2Triple i.left i.right i.left_ne_right).toLieSubalgebra ℂ)
    (radicalEndLie i) X]
  [Module.Finite ℂ X]

theorem raisingRadicalCyclicSpan_enveloping (z : X) (a : Enveloping n) {x : X}
    (hx : x∈raisingRadicalCyclicSpan (polynomialSl2Triple i.left i.right i.left_ne_right)
      (R := radicalEndLie i) z) :
    parabolicUpperEnveloping i X a x∈
      raisingRadicalCyclicSpan (polynomialSl2Triple i.left i.right i.left_ne_right)
        (R := radicalEndLie i) z := by
  rw [← parabolicOrbit_eq_cyclicSpan] at hx ⊢
  exact envelopingOrbit_stable _ z a hx

variable {M : Type u} [AddCommGroup M] [Module ℂ M]
  {E H : Module.End ℂ M} {ι : M →ₗ[ℂ] X}
  (C : IsRankOneCompletion
    (sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right))
    (sl2CartanElement (polynomialSl2Triple i.left i.right i.left_ne_right)) E H ι)

include C

/-- A cyclic upper module with a highest root-weight generator has a
completion cyclic under the upper algebra on its reflected lowest endpoint.
The proof uses only the exhibited completion and compatible actual actions. -/
theorem parabolicCompletion_endpoint_cyclic
    (ρ : Enveloping n →ₐ[ℂ] Module.End ℂ M) (z : M) (d : ℕ)
    (hcyc : ∀ m : M, ∃ a : Enveloping n, ρ a z=m)
    (hι : ∀ a m, ι (ρ a m)=parabolicUpperEnveloping i X a (ι m))
    (hh : ⁅sl2CartanElement (polynomialSl2Triple i.left i.right i.left_ne_right),ι z⁆=(d:ℂ) • ι z)
    (he : ⁅sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right),ι z⁆=0) :
    ∀ x : X, ∃ a : Enveloping n,
      parabolicUpperEnveloping i X a
        (primitiveStringVector (sl2LoweringElement
          (polynomialSl2Triple i.left i.right i.left_ne_right)) (ι z) d)=x := by
  let t := polynomialSl2Triple i.left i.right i.left_ne_right
  let η := primitiveStringVector (sl2LoweringElement t) (ι z) d
  let Y := raisingRadicalCyclicSpan t (R := radicalEndLie i) η
  have hηh : ⁅sl2CartanElement t,η⁆=-(d:ℂ) • η :=
    highestVector_endpoint_h (sl2SubalgebraTriple t) hh he
  have hηf : ⁅sl2LoweringElement t,η⁆=0 :=
    highestVector_endpoint_f (sl2SubalgebraTriple t) hh he
  have hz : ι z∈Y := by
    apply highestVector_mem_of_endpoint (sl2SubalgebraTriple t) hh he Y
    · intro x hx
      exact operatorCyclicSpan_stable
        (raisingRadicalOperators t (R := radicalEndLie i) (X := X)) η (.inl ()) hx
    · exact operatorCyclicSpan_generator _ η
  let Z := raisingRadicalCyclicLieSubmodule t (R := radicalEndLie i) η (-(d:ℂ)) hηh hηf
  have hb (m : M) : ι m∈Z := by
    obtain ⟨a,rfl⟩ := hcyc m
    rw [hι]
    exact raisingRadicalCyclicSpan_enveloping i η a hz
  intro x
  have hx : x∈Y := C.mem_of_boundary Z hb x
  change x∈raisingRadicalCyclicSpan
    (polynomialSl2Triple i.left i.right i.left_ne_right) (R := radicalEndLie i) η at hx
  rw [← parabolicOrbit_eq_cyclicSpan i X η] at hx
  exact hx

end
end Schubert.RS.Representation
