import Schubert.RS.Laurent
import Schubert.RS.CoefficientWindow
import Schubert.RS.ConcreteData

/-! Positive-root coordinates and the actual counterexample's truncation box. -/

namespace Schubert.RS

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
  simp only [Fin.val_mk, ← h]
  split_ifs <;> norm_num

def rootFirstCut (a b : Fin n) (hab : a < b) : Fin (n - 1) :=
  ⟨a.val, by have hb := b.isLt; have h : a.val < b.val := hab; omega⟩

@[simp] theorem rootDegree_first (a b : Fin n) (hab : a < b) :
    rootDegree a b (rootFirstCut a b hab) = 1 := by
  simp [rootFirstCut, hab]

/-- A high root power cannot enter the coordinatewise coefficient window. -/
theorem root_power_outside_window (a b : Fin n) (hab : a < b)
    (β : Fin (n - 1) →₀ ℕ) (r : ℕ) (hr : β (rootFirstCut a b hab) < r) :
    ¬r • rootDegree a b ≤ β := by
  intro h
  have hc := h (rootFirstCut a b hab)
  simp only [Finsupp.smul_apply, smul_eq_mul, rootDegree_first, mul_one] at hc
  omega

namespace Counterexample

/-- The target weight minus the two cyclic weights in the paper's extraction. -/
def targetDifference : Weight 28 := fun i => (c i : ℤ) - a i - b i

theorem beta_is_prefix : ∀ k : Fin 29,
    prefixWeight targetDifference k = (beta k : ℤ) := by decide

def coefficientBox : Fin 27 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun k => beta ⟨k.val + 1, by omega⟩)

theorem coefficientBox_le_eight (k : Fin 27) : coefficientBox k ≤ 8 := by
  change beta ⟨k.val + 1, by omega⟩ ≤ 8
  exact beta_le_eight _

theorem power_a_outside (i j : Fin 28) (hij : i < j) (h : a i < a j) :
    ¬(a j - a i + 1) • rootDegree i j ≤ coefficientBox := by
  apply root_power_outside_window i j hij
  have hb := coefficientBox_le_eight (rootFirstCut i j hij)
  have ha := ascent_gap_a i j h
  omega

theorem power_b_outside (i j : Fin 28) (hij : i < j) (h : b i < b j) :
    ¬(b j - b i + 1) • rootDegree i j ≤ coefficientBox := by
  apply root_power_outside_window i j hij
  have hb := coefficientBox_le_eight (rootFirstCut i j hij)
  have ha := ascent_gap_b i j h
  omega

theorem power_g_outside (i j : Fin 28) (hij : i < j) (h : g i < g j) :
    ¬(g j - g i + 1) • rootDegree i j ≤ coefficientBox := by
  apply root_power_outside_window i j hij
  have hb := coefficientBox_le_eight (rootFirstCut i j hij)
  have ha := ascent_gap_g i j h
  omega

end Counterexample
end
end Schubert.RS
