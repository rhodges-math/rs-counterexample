import Schubert.RS.Family.MarkedPairs
import Schubert.RS.Family.TermWeights
import Schubert.RS.Family.HallChoices
import Schubert.RS.Family.Sign
import Schubert.RS.FiniteCoefficientSums

/-! The full target Laurent coefficient of the two Hall polynomials, for
arbitrary positive p,q. Every target numerator term and source selection is
retained before the exact balance condition is imposed. -/

namespace Schubert.RS.Family
noncomputable section
variable {m p q : ℕ}

abbrev SlotLaurent (m : ℕ) := Laurent (2*m-1+1)

def slotVariable (j : Slot m) : SlotLaurent m := AddMonoidAlgebra.single (Pi.single j 1) 1

def targetNumerator (m : ℕ) : SlotLaurent m :=
  ∏ i : Fin m,(1-AddMonoidAlgebra.single (positiveRoot (slotLeft i) (slotRight i)) 1)

theorem hallPolynomial_monomials (hm : 0<m) (p : ℕ) :
    hallPolynomial (hallHeights hm p) slotVariable=
      ∑ s : PairedChoice m p,AddMonoidAlgebra.single (pairChoiceWeight s) (1 : ℤ) := by
  rw [hallPolynomial_paired_choices]
  apply Finset.sum_congr rfl
  intro s _
  simp only [slotVariable,AddMonoidAlgebra.prod_single,Finset.prod_const_one,
    AddMonoidAlgebra.single_mul_single,mul_one,pairChoiceWeight]

theorem targetNumerator_monomials (m : ℕ) :
    targetNumerator m=∑ f : Finset (Fin m),
      AddMonoidAlgebra.single (freePairWeight f) ((-1 : ℤ)^f.card) := by
  classical
  have hn (k : ℕ) : (-1 : SlotLaurent m)^k=
      AddMonoidAlgebra.single (0 : Weight (2*m-1+1)) ((-1 : ℤ)^k) := by
    symm
    change (AddMonoidAlgebra.singleZeroRingHom : ℤ →+* SlotLaurent m) ((-1 : ℤ)^k)=_
    rw [map_pow,map_neg,map_one]
  rw [targetNumerator,Finset.prod_sub]
  simp only [Finset.powerset_univ,Finset.prod_const_one,mul_one,AddMonoidAlgebra.prod_single]
  apply Finset.sum_congr rfl
  intro f _
  rw [hn,AddMonoidAlgebra.single_mul_single,zero_add,mul_one]
  rfl

theorem pairedHall_product_expansion (hm : 0<m) (p q : ℕ) :
    targetNumerator m*hallPolynomial (hallHeights hm p) slotVariable*
      hallPolynomial (hallHeights hm q) slotVariable=
    ∑ t : PairedTerm m p q,AddMonoidAlgebra.single (pairedTermWeight t) ((-1 : ℤ)^t.1.card) := by
  rw [targetNumerator_monomials,hallPolynomial_monomials,hallPolynomial_monomials]
  rw [triple_sum_product]
  apply Finset.sum_congr rfl
  intro t _
  simp only [AddMonoidAlgebra.single_mul_single,mul_one,pairedTermWeight]

theorem pairedHall_coefficient_marked_pairs (hm : 0<m) (p q : ℕ) :
    (targetNumerator m*hallPolynomial (hallHeights hm p) slotVariable*
      hallPolynomial (hallHeights hm q) slotVariable).coeff (fun _ => 1)=
      ∑ t : BalancedPairedTerm m p q,(-1 : ℤ)^t.val.1.card := by
  classical
  rw [pairedHall_product_expansion]
  exact coefficient_sum_single_subtype pairedTermWeight (fun t => (-1 : ℤ)^t.1.card)
    (fun _ => 1) BalancedTerm (pairedTermWeight_eq_one_iff hm)

theorem pairedHall_coefficient (hp : 0<p) (hq : 0<q) (h : p+q=m+1) :
    (targetNumerator m*hallPolynomial (hallHeights (by omega : 0<m) p) slotVariable*
      hallPolynomial (hallHeights (by omega : 0<m) q) slotVariable).coeff (fun _ => 1)=
      coefficientValue m p := by
  rw [pairedHall_coefficient_marked_pairs,marked_pair_signed_sum hp hq h]
  rfl

end
end Schubert.RS.Family
