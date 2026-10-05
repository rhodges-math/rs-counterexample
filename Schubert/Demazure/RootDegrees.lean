import Schubert.Demazure.Laurent
import Schubert.Demazure.PowerSeriesTruncation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-! Positive-root coordinates. -/

open Schubert

namespace Demazure

noncomputable section
variable {n : ℕ}

/-- Include the two endpoint prefixes, both zero for a root-lattice weight. -/
def prefixWeight (w : Weight n) (k : Fin (n + 1)) : ℤ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k.val), w j

theorem prefixWeight_add (v w : Weight n) (k : Fin (n + 1)) :
    prefixWeight (v + w) k = prefixWeight v k + prefixWeight w k := by
  simp [prefixWeight, Finset.sum_add_distrib]

theorem prefixWeight_sub (v w : Weight n) (k : Fin (n + 1)) :
    prefixWeight (v - w) k = prefixWeight v k - prefixWeight w k := by
  simp [prefixWeight, Finset.sum_sub_distrib]

theorem prefixWeight_single (a : Fin n) (k : Fin (n + 1)) :
    prefixWeight (Pi.single a (1 : ℤ)) k = if a.val < k.val then 1 else 0 := by
  simp [prefixWeight, Pi.single_apply]

theorem prefixWeight_positiveRoot (a b : Fin n) (hab : a < b) (k : Fin (n + 1)) :
    prefixWeight (positiveRoot a b) k =
      if a.val < k.val ∧ k.val ≤ b.val then 1 else 0 := by
  rw [positiveRoot, prefixWeight_sub, prefixWeight_single, prefixWeight_single]
  have h : a.val < b.val := hab
  split_ifs <;> omega

/-- A positive root has one in each of its simple-root coordinates. -/
def rootDegree (a b : Fin n) : Fin (n - 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun k => if a.val ≤ k.val ∧ k.val < b.val then 1 else 0)

@[simp] theorem rootDegree_apply (a b : Fin n) (k : Fin (n - 1)) :
    rootDegree a b k = if a.val ≤ k.val ∧ k.val < b.val then 1 else 0 := by
  simp [rootDegree]

theorem rootDegree_prefix (a b : Fin n) (hab : a < b) (k : Fin (n - 1)) :
    (rootDegree a b k : ℤ) =
      prefixWeight (positiveRoot a b) ⟨k.val + 1, by omega⟩ := by
  rw [rootDegree_apply, prefixWeight_positiveRoot a b hab]
  have h : (a.val ≤ k.val ∧ k.val < b.val) ↔
      (a.val < k.val + 1 ∧ k.val + 1 ≤ b.val) := by omega
  simp only [← h]
  split_ifs <;> norm_num

/-- The first cut `a` crossed by the positive root `(a, b)`. -/
def rootFirstCut (a b : Fin n) (hab : a < b) : Fin (n - 1) :=
  ⟨a.val, by have hb := b.isLt; have h : a.val < b.val := hab; omega⟩

theorem rootDegree_first (a b : Fin n) (hab : a < b) :
    rootDegree a b (rootFirstCut a b hab) = 1 := by
  simp [rootFirstCut, hab]

/-- A high root power cannot enter the coordinatewise coefficient window. -/
theorem root_power_outside_truncation (a b : Fin n) (hab : a < b)
    (β : Fin (n - 1) →₀ ℕ) (r : ℕ) (hr : β (rootFirstCut a b hab) < r) :
    ¬r • rootDegree a b ≤ β := by
  intro h
  have hc := h (rootFirstCut a b hab)
  simp only [Finsupp.smul_apply, smul_eq_mul, rootDegree_first, mul_one] at hc
  omega

end
end Demazure
