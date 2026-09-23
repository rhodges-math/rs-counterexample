import Schubert.RS.PrefixOrder
import Schubert.RS.Pairing
import Mathlib.Algebra.MonoidAlgebra.Support

/-! Prefix bounds on Laurent support and the support implication for the pairing. -/

namespace Schubert.RS
noncomputable section
variable {n : ℕ}
open scoped Pointwise

def PrefixSupported (a : Weight n) (p : Laurent n) : Prop :=
  ∀ w, p.coeff w ≠ 0 → PrefixLE a w

theorem PrefixLE.add {a b v w : Weight n} (h : PrefixLE a v) (h' : PrefixLE b w) :
    PrefixLE (a+b) (v+w) := by
  intro k
  rw [prefixWeight_add, prefixWeight_add]
  exact add_le_add (h k) (h' k)

theorem PrefixSupported.single (a : Weight n) (z : ℤ) :
    PrefixSupported a (AddMonoidAlgebra.single a z) := by
  intro w hw
  have he : a = w := by by_contra hn; simp [hn] at hw
  subst w
  exact PrefixLE.refl _

theorem PrefixSupported.one : PrefixSupported (0 : Weight n) 1 := by
  exact PrefixSupported.single (0 : Weight n) 1

theorem PrefixSupported.sub {a : Weight n} {p q : Laurent n}
    (hp : PrefixSupported a p) (hq : PrefixSupported a q) : PrefixSupported a (p-q) := by
  intro w hw
  by_cases h : p.coeff w = 0
  · apply hq w
    intro hqz
    simp [h, hqz] at hw
  · exact hp w h

theorem PrefixSupported.mul {a b : Weight n} {p q : Laurent n}
    (hp : PrefixSupported a p) (hq : PrefixSupported b q) :
    PrefixSupported (a+b) (p*q) := by
  intro w hw
  have hm := AddMonoidAlgebra.support_coeff_mul_subset p q (Finsupp.mem_support_iff.mpr hw)
  obtain ⟨v, hv, z, hz, rfl⟩ := Finset.mem_add.mp hm
  exact (hp v (Finsupp.mem_support_iff.mp hv)).add (hq z (Finsupp.mem_support_iff.mp hz))

theorem PrefixSupported.prod_zero {ι : Type*} (s : Finset ι) (f : ι → Laurent n)
    (hf : ∀ i ∈ s, PrefixSupported 0 (f i)) : PrefixSupported 0 (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PrefixSupported.one (n := n)
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    simpa using (hf i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem weylFactor_prefixSupported (n : ℕ) : PrefixSupported 0 (weylFactor n) := by
  unfold weylFactor
  apply PrefixSupported.prod_zero
  intro i hi
  apply PrefixSupported.prod_zero
  intro j hj
  apply PrefixSupported.one.sub
  intro w hw
  have he : positiveRoot i j = w := by by_contra hn; simp [hn] at hw
  rw [← he, ← rootWeight_rootDegree i j (Finset.mem_filter.mp hj).2]
  simpa using prefixLE_add_rootWeight (0 : Weight n) (rootDegree i j)

theorem pairing_monomial_coefficient (f : Polynomial n) (u : Composition n) :
    keyAtomPairing f (compositionMonomial u) =
      (toLaurent f * weylFactor n).coeff (fun i => (u i.rev : ℤ)) := by
  have hr : reverseNeg (toLaurent (compositionMonomial u)) =
      AddMonoidAlgebra.single (-(fun i => (u i.rev : ℤ))) 1 := by
    rw [compositionMonomial, toLaurent_monomial, reverseNeg_single]
    congr 1
  rw [keyAtomPairing, hr]
  calc
    _ = constantTerm (AddMonoidAlgebra.single (-(fun i => (u i.rev : ℤ))) 1 *
        (toLaurent f * weylFactor n)) := by congr 1; ring
    _ = _ := by rw [constantTerm_monomial_mul, neg_neg]

theorem pairing_monomial_support_bound (f : Polynomial n) (a : Weight n)
    (hf : PrefixSupported a (toLaurent f)) (u : Composition n)
    (h : keyAtomPairing f (compositionMonomial u) ≠ 0) :
    PrefixLE a (fun i => (u i.rev : ℤ)) := by
  rw [pairing_monomial_coefficient] at h
  simpa using (hf.mul (weylFactor_prefixSupported n)) _ h

end
end Schubert.RS
