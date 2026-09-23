import Schubert.RS.AtomBasis

/-! Integral atom expansions and their unique coefficients, obtained from
key-atom orthogonality under explicit representation-theoretic hypotheses. -/

namespace Schubert.RS
noncomputable section
open Representation
variable {n : ℕ}

def integralAtomExpansion (f : Polynomial n) : Composition n →₀ ℤ :=
  ∑ u : BoxIndex n f.totalDegree,Finsupp.single (boxComposition u)
    (rectangleCoefficient f.totalDegree (boxComposition u) f)

def atomCoefficient (f : Polynomial n) (u : Composition n) : ℤ := integralAtomExpansion f u

theorem integralAtomExpansion_spec
    (hJP : ∀ u : Composition n,CompositionFlagJosephPolo u)
    (hDCF : ∀ u : Composition n,CompositionFlagDemazureCharacter u) (hpbw : HasOrderedPBWBasis n)
    (f : Polynomial n) : f=(integralAtomExpansion f).sum (fun u z => z • atom u) := by
  change f=Finsupp.linearCombination ℤ atom (integralAtomExpansion f)
  rw [integralAtomExpansion,map_sum]
  simp only [Finsupp.linearCombination_single]
  exact boxed_atom_expansion hJP hDCF hpbw f.totalDegree f (polynomial_mem_degree_box f)

theorem integralAtomExpansion_unique
    (hJP : ∀ u : Composition n,CompositionFlagJosephPolo u)
    (hDCF : ∀ u : Composition n,CompositionFlagDemazureCharacter u) (hpbw : HasOrderedPBWBasis n)
    (f : Polynomial n) (t : Composition n →₀ ℤ)
    (ht : f=t.sum (fun u z => z • atom u)) : t=integralAtomExpansion f := by
  ext u
  let w:=Finset.univ.sup u
  have hu : ∀ i,u i≤w := fun i => Finset.le_sup (Finset.mem_univ i)
  rw [← rectangleCoefficient_expansion compositionFlagTorus compositionFlagGenerator
    hJP hDCF hpbw w u hu t,← ht,
    integralAtomExpansion_spec hJP hDCF hpbw f,
    rectangleCoefficient_expansion compositionFlagTorus compositionFlagGenerator hJP hDCF hpbw w u hu]
  rw [← integralAtomExpansion_spec hJP hDCF hpbw f]

theorem existsUnique_integral_atom_expansion
    (hJP : ∀ u : Composition n,CompositionFlagJosephPolo u)
    (hDCF : ∀ u : Composition n,CompositionFlagDemazureCharacter u) (hpbw : HasOrderedPBWBasis n)
    (f : Polynomial n) : ∃! t : Composition n →₀ ℤ,f=t.sum (fun u z => z • atom u) :=
  ⟨integralAtomExpansion f,integralAtomExpansion_spec hJP hDCF hpbw f,
    fun t ht => integralAtomExpansion_unique hJP hDCF hpbw f t ht⟩

theorem atomCoefficient_eq_rectangleCoefficient
    (hJP : ∀ u : Composition n,CompositionFlagJosephPolo u)
    (hDCF : ∀ u : Composition n,CompositionFlagDemazureCharacter u) (hpbw : HasOrderedPBWBasis n)
    (w : ℕ) (c : Composition n) (hc : ∀ i,c i≤w) (f : Polynomial n) :
    atomCoefficient f c=rectangleCoefficient w c f := by
  rw [integralAtomExpansion_spec hJP hDCF hpbw f,
    rectangleCoefficient_expansion compositionFlagTorus compositionFlagGenerator hJP hDCF hpbw w c hc]
  unfold atomCoefficient
  rw [← integralAtomExpansion_spec hJP hDCF hpbw f]

end
end Schubert.RS

