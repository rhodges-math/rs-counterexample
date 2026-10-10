import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# The rank-28 counterexample data

These theorems certify the input and window arithmetic. They do not by
themselves identify an atom coefficient; that connection is a separate proof.
-/

namespace Schubert.RS.Counterexample

def a : Fin 28 → ℕ :=
  ![0,0,0,0,8,8,8,8,16,24,32,40,48,56,64,0,0,0,8,8,8,64,56,48,40,32,24,16]

def b : Fin 28 → ℕ :=
  ![8,8,8,8,0,0,0,0,64,56,48,40,32,24,16,8,8,8,0,0,0,16,24,32,40,48,56,64]

def c : Fin 28 → ℕ :=
  ![9,9,9,9,9,9,9,9,79,79,79,79,79,79,79,9,9,9,9,9,9,79,79,79,79,79,79,79]

def g (i : Fin 28) : ℕ := 79 - c i

/-- Prefix values at indices zero through 28, including both zero endpoints. -/
def beta : Fin 29 → ℕ :=
  ![0,1,2,3,4,5,6,7,8,7,6,5,4,3,2,1,2,3,4,5,6,7,6,5,4,3,2,1,0]

theorem degree_a : ∑ i, a i = 616 := by
  norm_num [a, Fin.sum_univ_succ]

theorem degree_b : ∑ i, b i = 616 := by
  norm_num [b, Fin.sum_univ_succ]

theorem degree_c : ∑ i, c i = 1232 := by
  norm_num [c, Fin.sum_univ_succ]

theorem degree_balance : (∑ i, a i) + (∑ i, b i) = ∑ i, c i := by
  rw [degree_a, degree_b, degree_c]

theorem c_le : ∀ i, c i ≤ 79 := by decide

theorem g_add_c (i : Fin 28) : g i + c i = 79 :=
  Nat.sub_add_cancel (c_le i)

theorem beta_le_eight : ∀ i, beta i ≤ 8 := by decide

theorem beta_recurrence : ∀ i : Fin 28,
    (beta i.succ : ℤ) - beta i.castSucc = (c i : ℤ) - a i - b i := by decide

theorem ascent_gap_a : ∀ i j, a i < a j → 9 ≤ a j - a i + 1 := by decide

theorem ascent_gap_b : ∀ i j, b i < b j → 9 ≤ b j - b i + 1 := by decide

theorem ascent_gap_g : ∀ i j, g i < g j → 71 ≤ g j - g i + 1 := by decide

/-- The signed count obtained after source extraction. -/
theorem signed_count :
    2 * (Nat.choose 7 3 : ℤ) * Nat.choose 7 4 -
      7 * (Nat.choose 6 3 : ℤ) ^ 2 = -350 := by
  norm_num [Nat.choose]

end Schubert.RS.Counterexample
