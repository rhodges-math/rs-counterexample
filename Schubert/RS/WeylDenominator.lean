import Schubert.RS.LaurentSymmetry
import Mathlib.Data.Fintype.BigOperators

/-! The finite Weyl denominator and its coordinate symmetries. -/

namespace Schubert.RS

open FinPermutation
noncomputable section
variable {n : ℕ}

theorem weylFactor_eq_pair_product :
    weylFactor n = ∏ r : Fin n × Fin n,
      if r.1 < r.2 then (1 - AddMonoidAlgebra.single (positiveRoot r.1 r.2) 1) else 1 := by
  simp only [weylFactor, Fintype.prod_prod_type, Finset.prod_filter]

theorem reverseNegWeight_positiveRoot (a b : Fin n) :
    reverseNegWeight (positiveRoot a b) = positiveRoot b.rev a.rev := by
  ext k
  simp only [reverseNegWeight, positiveRoot, AddEquiv.coe_mk, Equiv.coe_fn_mk,
    Pi.sub_apply, Pi.single_apply]
  have ha : k.rev = a ↔ k = a.rev := by
    constructor <;> intro h
    · simpa using congrArg Fin.rev h
    · simpa [h]
  have hb : k.rev = b ↔ k = b.rev := by
    constructor <;> intro h
    · simpa using congrArg Fin.rev h
    · simpa [h]
  simp only [ha, hb]
  ring

def reverseRootPair : (Fin n × Fin n) ≃ (Fin n × Fin n) where
  toFun r := (r.2.rev, r.1.rev)
  invFun r := (r.2.rev, r.1.rev)
  left_inv r := by simp
  right_inv r := by simp

@[simp] theorem reverseNeg_single (a : Weight n) (z : ℤ) :
    reverseNeg (AddMonoidAlgebra.single a z) =
      AddMonoidAlgebra.single (reverseNegWeight a) z :=
  AddMonoidAlgebra.mapDomainRingEquiv_single _ _ _

/-- The reversal and inversion in the paper preserve the upper-root denominator. -/
theorem reverseNeg_weylFactor : reverseNeg (weylFactor n) = weylFactor n := by
  rw [weylFactor_eq_pair_product, map_prod]
  calc
    _ = ∏ r : Fin n × Fin n,
      if (reverseRootPair r).1 < (reverseRootPair r).2 then
        ((1 : Laurent n) - AddMonoidAlgebra.single
          (positiveRoot (reverseRootPair r).1 (reverseRootPair r).2) 1) else 1 := by
        apply Finset.prod_congr rfl
        intro r _
        by_cases h : r.1 < r.2
        · simp [reverseRootPair, h, reverseNegWeight_positiveRoot]
        · simp [reverseRootPair, h]
    _ = _ := reverseRootPair.prod_comp (fun r : Fin n × Fin n =>
      if r.1 < r.2 then (1 : Laurent n) -
        AddMonoidAlgebra.single (positiveRoot r.1 r.2) 1 else 1)

theorem weightSwap_positiveRoot (i : AdjacentPosition n) (a b : Fin n) :
    weightSwap i (positiveRoot a b) =
      positiveRoot (adjacentTransposition i a) (adjacentTransposition i b) := by
  ext k
  have he (a : Fin n) : adjacentTransposition i k = a ↔ k = adjacentTransposition i a := by
    constructor <;> intro h
    · simpa [adjacentTransposition] using congrArg (adjacentTransposition i) h
    · simpa [h, adjacentTransposition]
  simp [weightSwap, positiveRoot, Pi.single_apply, he]

/-- Swapping two adjacent coordinates permutes all positive roots except
the simple root between those coordinates. -/
theorem adjacent_preserves_other_positive_pairs (i : AdjacentPosition n) (a b : Fin n) :
    (adjacentTransposition i a < adjacentTransposition i b ∧
      (adjacentTransposition i a, adjacentTransposition i b) ≠ (i.left, i.right)) ↔
      (a < b ∧ (a, b) ≠ (i.left, i.right)) := by
  by_cases hal : a = i.left <;> by_cases har : a = i.right <;>
    by_cases hbl : b = i.left <;> by_cases hbr : b = i.right <;>
    simp_all [adjacentTransposition, Equiv.swap_apply_def, Prod.ext_iff,
      Fin.ext_iff, Fin.lt_def, AdjacentPosition.right_val, -Fin.val_fin_lt] <;> omega

def swapRootPair (i : AdjacentPosition n) : (Fin n × Fin n) ≃ (Fin n × Fin n) :=
  Equiv.prodCongr (adjacentTransposition i) (adjacentTransposition i)

def weylRemainder (i : AdjacentPosition n) : Laurent n :=
  ∏ r : Fin n × Fin n, if r.1 < r.2 ∧ r ≠ (i.left, i.right) then
    (1 - AddMonoidAlgebra.single (positiveRoot r.1 r.2) 1) else 1

theorem weylFactor_split (i : AdjacentPosition n) :
    weylFactor n = (1 - AddMonoidAlgebra.single (positiveRoot i.left i.right) 1) *
      weylRemainder i := by
  have ht (r : Fin n × Fin n) :
      (if r.1 < r.2 then (1 : Laurent n) -
        AddMonoidAlgebra.single (positiveRoot r.1 r.2) 1 else 1) =
      (if r = (i.left, i.right) then (1 : Laurent n) -
        AddMonoidAlgebra.single (positiveRoot i.left i.right) 1 else 1) *
      (if r.1 < r.2 ∧ r ≠ (i.left, i.right) then (1 : Laurent n) -
        AddMonoidAlgebra.single (positiveRoot r.1 r.2) 1 else 1) := by
    by_cases h : r = (i.left, i.right)
    · subst r
      simp [i.left_lt_right]
    · simp [h]
  rw [weylFactor_eq_pair_product]
  simp_rw [ht]
  rw [Finset.prod_mul_distrib]
  simp only [Fintype.prod_ite_eq']
  rfl

theorem laurentSwap_weylRemainder (i : AdjacentPosition n) :
    laurentSwap i (weylRemainder i) = weylRemainder i := by
  rw [weylRemainder, map_prod]
  calc
    _ = ∏ r : Fin n × Fin n,
      if (swapRootPair i r).1 < (swapRootPair i r).2 ∧
        swapRootPair i r ≠ (i.left, i.right) then
        (1 : Laurent n) - AddMonoidAlgebra.single
          (positiveRoot (swapRootPair i r).1 (swapRootPair i r).2) 1 else 1 := by
        apply Finset.prod_congr rfl
        intro r _
        have h := adjacent_preserves_other_positive_pairs i r.1 r.2
        change ((swapRootPair i r).1 < (swapRootPair i r).2 ∧
          swapRootPair i r ≠ (i.left, i.right)) ↔
          (r.1 < r.2 ∧ r ≠ (i.left, i.right)) at h
        simp only [h]
        split_ifs <;> simp [weightSwap_positiveRoot, swapRootPair]
    _ = _ := (swapRootPair i).prod_comp (fun r : Fin n × Fin n =>
      if r.1 < r.2 ∧ r ≠ (i.left, i.right) then (1 : Laurent n) -
        AddMonoidAlgebra.single (positiveRoot r.1 r.2) 1 else 1)

end
end Schubert.RS
