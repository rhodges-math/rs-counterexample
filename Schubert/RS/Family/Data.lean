import Schubert.RS.ConcreteData
import Mathlib.Tactic.Linarith

/-! The exact block-ordered composition family in Theorem 1.1. The first two
class labels denote sources; labels 2,...,m+1 denote paired targets. -/

namespace Schubert.RS.Family

structure Parameters where
  p : ℕ
  q : ℕ
  K : ℕ
  p_pos : 0 < p
  q_pos : 0 < q
  scale_bound : p+q ≤ K

namespace Parameters

def m (P : Parameters) : ℕ := P.p+P.q-1
def rank (P : Parameters) : ℕ := 4*P.m
def rectangle (P : Parameters) : ℕ := (P.m+3)*P.K-1

theorem pq_eq (P : Parameters) : P.p+P.q=P.m+1 := by
  have hp := P.p_pos
  have hq := P.q_pos
  unfold m
  omega

theorem m_pos (P : Parameters) : 0 < P.m := by
  have hp := P.p_pos
  have hq := P.q_pos
  have h := P.pq_eq
  omega

theorem p_le_m (P : Parameters) : P.p ≤ P.m := by
  have hq := P.q_pos
  have h := P.pq_eq
  omega

theorem q_le_m (P : Parameters) : P.q ≤ P.m := by
  have hp := P.p_pos
  have h := P.pq_eq
  omega

theorem K_bound (P : Parameters) : P.m+1 ≤ P.K := by
  rw [← P.pq_eq]
  exact P.scale_bound

theorem K_pos (P : Parameters) : 0 < P.K := by
  have h := P.K_bound
  omega

end Parameters

def coordinateClass (P : Parameters) (i : Fin P.rank) : Fin (P.m+2) :=
  ⟨if i.val < P.p then 0
   else if i.val < P.m+1 then 1
   else if i.val < 2*P.m+1 then i.val-(P.m+1)+2
   else if i.val < 2*P.m+P.p then 0
   else if i.val < 3*P.m then 1
   else 4*P.m-1-i.val+2, by
      have hi := i.isLt
      change i.val < 4*P.m at hi
      have hm := P.m_pos
      split_ifs <;> omega⟩

def sourceClass (P : Parameters) (i : Fin P.rank) : Prop :=
  (coordinateClass P i).val < 2

instance (P : Parameters) (i : Fin P.rank) : Decidable (sourceClass P i) :=
  inferInstanceAs (Decidable (_ < _))

def a (P : Parameters) (i : Fin P.rank) : ℕ := (coordinateClass P i).val*P.K

def b (P : Parameters) (i : Fin P.rank) : ℕ :=
  (if (coordinateClass P i).val=0 then 1
   else if (coordinateClass P i).val=1 then 0
   else P.m+3-(coordinateClass P i).val)*P.K

def c (P : Parameters) (i : Fin P.rank) : ℕ :=
  if sourceClass P i then P.K+1 else P.rectangle

def g (P : Parameters) (i : Fin P.rank) : ℕ := P.rectangle-c P i

theorem sourceClass_iff (P : Parameters) (i : Fin P.rank) :
    sourceClass P i ↔ i.val < P.m+1 ∨ (2*P.m+1 ≤ i.val ∧ i.val < 3*P.m) := by
  have hi := i.isLt
  change i.val < 4*P.m at hi
  have hp := P.p_pos
  have hpm := P.p_le_m
  have hm := P.m_pos
  unfold sourceClass coordinateClass
  split_ifs <;> simp only <;> omega

theorem early_source_A (P : Parameters) (i : Fin P.rank) (h : i.val < P.p) :
    (coordinateClass P i).val=0 := by simp [coordinateClass,h]

theorem early_source_B (P : Parameters) (i : Fin P.rank)
    (h₁ : P.p ≤ i.val) (h₂ : i.val < P.p+P.q) :
    (coordinateClass P i).val=1 := by
  have h₃ : i.val < P.m+1 := by rwa [P.pq_eq] at h₂
  simp [coordinateClass,show ¬i.val < P.p by omega,h₃]

theorem early_target (P : Parameters) (i : Fin P.rank)
    (h₁ : P.m+1 ≤ i.val) (h₂ : i.val < 2*P.m+1) :
    (coordinateClass P i).val=i.val-(P.m+1)+2 := by
  have hp := P.p_le_m
  simp [coordinateClass,show ¬i.val < P.p by omega,show ¬i.val < P.m+1 by omega,h₂]

theorem middle_source_A (P : Parameters) (i : Fin P.rank)
    (h₁ : 2*P.m+1 ≤ i.val) (h₂ : i.val < 2*P.m+P.p) :
    (coordinateClass P i).val=0 := by
  have hp := P.p_le_m
  simp [coordinateClass,show ¬i.val < P.p by omega,
    show ¬i.val < P.m+1 by omega,show ¬i.val < 2*P.m+1 by omega,h₂]

theorem middle_source_B (P : Parameters) (i : Fin P.rank)
    (h₁ : 2*P.m+P.p ≤ i.val) (h₂ : i.val < 3*P.m) :
    (coordinateClass P i).val=1 := by
  have hp := P.p_pos
  have hpm := P.p_le_m
  simp [coordinateClass,show ¬i.val < P.p by omega,
    show ¬i.val < P.m+1 by omega,show ¬i.val < 2*P.m+1 by omega,
    show ¬i.val < 2*P.m+P.p by omega,h₂]

theorem late_target (P : Parameters) (i : Fin P.rank) (h : 3*P.m ≤ i.val) :
    (coordinateClass P i).val=4*P.m-1-i.val+2 := by
  have hp := P.p_le_m
  have hm := P.m_pos
  simp [coordinateClass,show ¬i.val < P.p by omega,
    show ¬i.val < P.m+1 by omega,show ¬i.val < 2*P.m+1 by omega,
    show ¬i.val < 2*P.m+P.p by omega,show ¬i.val < 3*P.m by omega]

/-- Parameters for the rank-28 example. -/
def rank28Parameters : Parameters := ⟨4,4,8,by decide,by decide,by decide⟩

theorem rank28_a : a rank28Parameters = Counterexample.a := by
  apply funext
  change ∀ i : Fin 28, a rank28Parameters i=Counterexample.a i
  simp only [a,b,c,g,sourceClass,coordinateClass,rank28Parameters,Parameters.rank,Parameters.m,Parameters.rectangle]
  decide
theorem rank28_b : b rank28Parameters = Counterexample.b := by
  apply funext
  change ∀ i : Fin 28, b rank28Parameters i=Counterexample.b i
  simp only [a,b,c,g,sourceClass,coordinateClass,rank28Parameters,Parameters.rank,Parameters.m,Parameters.rectangle]
  decide
theorem rank28_c : c rank28Parameters = Counterexample.c := by
  apply funext
  change ∀ i : Fin 28, c rank28Parameters i=Counterexample.c i
  simp only [a,b,c,g,sourceClass,coordinateClass,rank28Parameters,Parameters.rank,Parameters.m,Parameters.rectangle]
  decide
theorem rank28_g : g rank28Parameters = Counterexample.g := by
  apply funext
  change ∀ i : Fin 28, g rank28Parameters i=Counterexample.g i
  simp only [a,b,c,g,sourceClass,coordinateClass,rank28Parameters,Parameters.rank,Parameters.m,Parameters.rectangle]
  decide

end Schubert.RS.Family

