import Schubert.RS.FullWeightSupport
import Mathlib.Algebra.MonoidAlgebra.Support

/-! Finite polynomials in nonnegative simple-root coordinates. -/

namespace Schubert.RS
noncomputable section
open Representation
open scoped Pointwise
variable {n : ℕ}

def RootSupported (p : Laurent n) : Prop :=
  ∀ w, p.coeff w ≠ 0 → ∃ d : RootDegree n, rootWeight d = w

def rootCoordinateEmbedding : MvPolynomial (Fin (n-1)) ℤ →+* Laurent n :=
  AddMonoidAlgebra.mapDomainRingHom ℤ rootWeightHom

def rootCoordinates (p : Laurent n) : MvPolynomial (Fin (n-1)) ℤ :=
  AddMonoidAlgebra.comapDomain rootWeight rootWeight_injective p

@[simp] theorem rootCoordinates_coeff (p : Laurent n) (d : RootDegree n) :
    MvPolynomial.coeff d (rootCoordinates p) = p.coeff (rootWeight d) := by
  simp [rootCoordinates, MvPolynomial.coeff, AddMonoidAlgebra.coeff_comapDomain]

theorem rootCoordinateEmbedding_injective :
    Function.Injective (rootCoordinateEmbedding (n := n)) :=
  AddMonoidAlgebra.mapDomain_injective rootWeight_injective

theorem rootCoordinateEmbedding_rootCoordinates (p : Laurent n) (hp : RootSupported p) :
    rootCoordinateEmbedding (rootCoordinates p) = p := by
  apply AddMonoidAlgebra.mapDomain_comapDomain
  intro w hw
  exact hp w (Finsupp.mem_support_iff.mp hw)

theorem RootSupported.single (d : RootDegree n) (z : ℤ) :
    RootSupported (AddMonoidAlgebra.single (rootWeight d) z) := by
  intro w hw
  refine ⟨d, ?_⟩
  by_contra hn
  simp [hn] at hw

theorem RootSupported.one : RootSupported (1 : Laurent n) := by
  change RootSupported (AddMonoidAlgebra.single (0 : Weight n) 1)
  rw [← rootWeight_zero]
  exact RootSupported.single _ _

theorem RootSupported.sub {p q : Laurent n} (hp : RootSupported p) (hq : RootSupported q) :
    RootSupported (p-q) := by
  intro w hw
  by_cases h : p.coeff w = 0
  · apply hq w
    intro hqz
    simp [h, hqz] at hw
  · exact hp w h

theorem RootSupported.mul {p q : Laurent n} (hp : RootSupported p) (hq : RootSupported q) :
    RootSupported (p*q) := by
  intro w hw
  have hm := AddMonoidAlgebra.support_coeff_mul_subset p q (Finsupp.mem_support_iff.mpr hw)
  obtain ⟨v, hv, z, hz, rfl⟩ := Finset.mem_add.mp hm
  obtain ⟨d, rfl⟩ := hp v (Finsupp.mem_support_iff.mp hv)
  obtain ⟨e, rfl⟩ := hq z (Finsupp.mem_support_iff.mp hz)
  exact ⟨d+e, rootWeight_add d e⟩

theorem RootSupported.prod {ι : Type*} (s : Finset ι) (f : ι → Laurent n)
    (hf : ∀ i ∈ s, RootSupported (f i)) : RootSupported (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RootSupported.one (n := n)
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem rootCoordinates_mul (p q : Laurent n) (hp : RootSupported p) (hq : RootSupported q) :
    rootCoordinates (p*q) = rootCoordinates p * rootCoordinates q := by
  apply rootCoordinateEmbedding_injective
  rw [map_mul, rootCoordinateEmbedding_rootCoordinates _ (hp.mul hq),
    rootCoordinateEmbedding_rootCoordinates p hp, rootCoordinateEmbedding_rootCoordinates q hq]

theorem weylFactor_rootSupported (n : ℕ) : RootSupported (weylFactor n) := by
  unfold weylFactor
  apply RootSupported.prod
  intro i hi
  apply RootSupported.prod
  intro j hj
  apply RootSupported.one.sub
  rw [← rootWeight_rootDegree i j (Finset.mem_filter.mp hj).2]
  exact RootSupported.single _ _

def normalizedKey (u : Composition n) : Laurent n :=
  AddMonoidAlgebra.single (-(fun i => (u i : ℤ))) 1 * toLaurent (key u)

@[simp] theorem normalizedKey_coeff (u : Composition n) (d : RootDegree n) :
    (normalizedKey u).coeff (rootWeight d) =
      (toLaurent (key u)).coeff (weightOfRootDegree u d) := by
  simp [normalizedKey, weightOfRootDegree]

theorem normalizedKey_rootSupported {E : Type*} [AddCommGroup E] [Module ℂ E]
    [Module (Enveloping n) E] [IsScalarTower ℂ (Enveloping n) E]
    (u : Composition n) (ρ : DiagonalTorus n →* Module.End ℂ E) (ξ : E)
    (hJP : HasJosephPoloPresentation u ρ ξ) (hDCF : HasDemazureCharacter u ρ)
    (hpbw : HasOrderedPBWBasis n) : RootSupported (normalizedKey u) := by
  intro w hw
  simp only [normalizedKey, AddMonoidAlgebra.coeff_single_mul_apply, one_mul, neg_neg] at hw
  obtain ⟨d, hd⟩ := key_support_positive_root_cone u ρ ξ hJP hDCF hpbw _ hw
  refine ⟨d, ?_⟩
  change (fun i => (u i : ℤ)) + rootWeight d = (fun i => (u i : ℤ)) + w at hd
  exact add_left_cancel hd

end
end Schubert.RS
