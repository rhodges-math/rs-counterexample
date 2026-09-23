import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Lean.Elab.Tactic.Omega

/-! Tail exchange at an intersection, the cancellation operation in the
Hall determinant proof. Paths are recorded by diagonal time: each north
or east step increases that time by one. -/

namespace Schubert.RS

variable {V : Type*} {d T : ℕ}

/-- Exchange the strict tails of two labelled paths after a common time. -/
def swapPathTails (p : Fin d → Fin (T + 1) → V) (t : Fin (T + 1))
    (a b : Fin d) (i : Fin d) (k : Fin (T + 1)) : V :=
  if k ≤ t then p i k else p (Equiv.swap a b i) k

theorem swapPathTails_prefix (p : Fin d → Fin (T + 1) → V)
    (t : Fin (T + 1)) (a b i : Fin d) (k : Fin (T + 1)) (hk : k ≤ t) :
    swapPathTails p t a b i k = p i k := by simp [swapPathTails, hk]

theorem swapPathTails_involutive (p : Fin d → Fin (T + 1) → V)
    (t : Fin (T + 1)) (a b : Fin d) :
    swapPathTails (swapPathTails p t a b) t a b = p := by
  funext i k
  by_cases hk : k ≤ t <;> simp [swapPathTails, hk]

theorem swapPathTails_cut (p : Fin d → Fin (T + 1) → V)
    (t : Fin (T + 1)) (a b i : Fin d) (hab : p a t = p b t) :
    p (Equiv.swap a b i) t = p i t := by
  by_cases ha : i = a
  · subst i; simpa using hab.symm
  by_cases hb : i = b
  · subst i; simpa using hab
  rw [Equiv.swap_apply_of_ne_of_ne ha hb]

/-- Local path constraints are preserved; the only mixed edge crosses the
cut, where the exchanged paths have the same vertex. -/
theorem swapPathTails_edges (p : Fin d → Fin (T + 1) → V)
    (t : Fin (T + 1)) (a b : Fin d) (hab : p a t = p b t)
    (E : Fin T → V → V → Prop)
    (hp : ∀ i k, E k (p i k.castSucc) (p i k.succ)) :
    ∀ i k, E k (swapPathTails p t a b i k.castSucc)
      (swapPathTails p t a b i k.succ) := by
  intro i k
  by_cases hn : k.succ ≤ t
  · have ho : k.castSucc ≤ t := by have h : k.val + 1 ≤ t.val := hn; change k.val ≤ t.val; omega
    simpa only [swapPathTails, if_pos hn, if_pos ho] using hp i k
  · by_cases ho : k.castSucc ≤ t
    · have ht : k.castSucc = t := by
        have h : ¬ k.val + 1 ≤ t.val := hn
        have h' : k.val ≤ t.val := ho
        apply Fin.ext
        change k.val = t.val
        omega
      rw [swapPathTails, if_pos ho, swapPathTails, if_neg hn]
      rw [ht, ← swapPathTails_cut p t a b i hab, ← ht]
      exact hp (Equiv.swap a b i) k
    · simpa only [swapPathTails, if_neg hn, if_neg ho] using hp (Equiv.swap a b i) k

/-- At each diagonal time, tail exchange preserves the product of edge
weights over all path labels. It therefore preserves the full path weight. -/
theorem swapPathTails_edge_weight {R : Type*} [CommMonoid R]
    (p : Fin d → Fin (T + 1) → V) (t : Fin (T + 1))
    (a b : Fin d) (hab : p a t = p b t) (w : Fin T → V → V → R) (k : Fin T) :
    (∏ i, w k (swapPathTails p t a b i k.castSucc)
      (swapPathTails p t a b i k.succ)) = ∏ i, w k (p i k.castSucc) (p i k.succ) := by
  by_cases hn : k.succ ≤ t
  · have ho : k.castSucc ≤ t := by have h : k.val + 1 ≤ t.val := hn; change k.val ≤ t.val; omega
    simp only [swapPathTails, if_pos hn, if_pos ho]
  · by_cases ho : k.castSucc ≤ t
    · have ht : k.castSucc = t := by
        have h : ¬ k.val + 1 ≤ t.val := hn
        have h' : k.val ≤ t.val := ho
        apply Fin.ext
        change k.val = t.val
        omega
      simp only [swapPathTails, if_pos ho, if_neg hn]
      have he (i : Fin d) : p i k.castSucc = p (Equiv.swap a b i) k.castSucc := by
        rw [ht]; exact (swapPathTails_cut p t a b i hab).symm
      calc
        _ = ∏ i, w k (p (Equiv.swap a b i) k.castSucc) (p (Equiv.swap a b i) k.succ) := by
          apply Finset.prod_congr rfl
          intro i _
          exact congrArg (fun x => w k x (p (Equiv.swap a b i) k.succ)) (he i)
        _ = _ := Equiv.prod_comp (Equiv.swap a b) (fun i => w k (p i k.castSucc) (p i k.succ))
    · simp only [swapPathTails, if_neg ho, if_neg hn]
      exact Equiv.prod_comp (Equiv.swap a b) (fun i => w k (p i k.castSucc) (p i k.succ))

theorem swapPathTails_weight {R : Type*} [CommMonoid R]
    (p : Fin d → Fin (T + 1) → V) (t : Fin (T + 1))
    (a b : Fin d) (hab : p a t = p b t) (w : Fin T → V → V → R) :
    (∏ k, ∏ i, w k (swapPathTails p t a b i k.castSucc)
      (swapPathTails p t a b i k.succ)) = ∏ k, ∏ i, w k (p i k.castSucc) (p i k.succ) := by
  apply Finset.prod_congr rfl
  intro k _
  exact swapPathTails_edge_weight p t a b hab w k

end Schubert.RS
