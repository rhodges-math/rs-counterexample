import Schubert.RS.Family.Slots
import Schubert.RS.Laurent

/-! Exact exponent conservation at both slots of every target pair. -/

namespace Schubert.RS.Family
noncomputable section
variable {m p q : ℕ}

def pairChoiceWeight (s : PairedChoice m p) : Weight (2*m-1+1) :=
  (∑ i ∈ s.val.1, Pi.single (slotRight i) 1) + ∑ i ∈ s.val.2, Pi.single (slotLeft i) 1

def freePairWeight (f : Finset (Fin m)) : Weight (2*m-1+1) :=
  ∑ i ∈ f, positiveRoot (slotLeft i) (slotRight i)

def pairedTermWeight (t : PairedTerm m p q) : Weight (2*m-1+1) :=
  freePairWeight t.1 + pairChoiceWeight t.2.1 + pairChoiceWeight t.2.2

def memberInt (s : Finset (Fin m)) (i : Fin m) : ℤ := if i ∈ s then 1 else 0

theorem sum_single_same {d : ℕ} (f : Fin m → Fin d) (hf : Function.Injective f)
    (s : Finset (Fin m)) (i : Fin m) :
    (∑ j ∈ s, (Pi.single (f j) (1 : ℤ) : Weight d)) (f i) = memberInt s i := by
  classical
  simp only [Finset.sum_apply, Pi.single_apply, hf.eq_iff]
  simp [memberInt, eq_comm]

theorem sum_single_other {d : ℕ} (f : Fin m → Fin d) (z : Fin d)
    (h : ∀ j, f j ≠ z) (s : Finset (Fin m)) :
    (∑ j ∈ s, (Pi.single (f j) (1 : ℤ) : Weight d)) z = 0 := by
  simp [Finset.sum_apply, Pi.single_apply, h]

theorem pairChoiceWeight_right (s : PairedChoice m p) (i : Fin m) :
    pairChoiceWeight s (slotRight i) = memberInt s.val.1 i := by
  rw [pairChoiceWeight, Pi.add_apply, sum_single_same _ slotRight_injective,
    sum_single_other _ _ (fun j => slots_ne j i), add_zero]

theorem pairChoiceWeight_left (s : PairedChoice m p) (i : Fin m) :
    pairChoiceWeight s (slotLeft i) = memberInt s.val.2 i := by
  rw [pairChoiceWeight, Pi.add_apply,
    sum_single_other _ _ (fun j => (slots_ne i j).symm),
    sum_single_same _ slotLeft_injective, zero_add]

theorem freePairWeight_right (f : Finset (Fin m)) (i : Fin m) :
    freePairWeight f (slotRight i) = -memberInt f i := by
  simp only [freePairWeight, positiveRoot, Finset.sum_sub_distrib, Pi.sub_apply]
  rw [sum_single_other _ _ (fun j => slots_ne j i),
    sum_single_same _ slotRight_injective, zero_sub]

theorem freePairWeight_left (f : Finset (Fin m)) (i : Fin m) :
    freePairWeight f (slotLeft i) = memberInt f i := by
  simp only [freePairWeight, positiveRoot, Finset.sum_sub_distrib, Pi.sub_apply]
  rw [sum_single_same _ slotLeft_injective,
    sum_single_other _ _ (fun j => (slots_ne i j).symm), sub_zero]

theorem pairedTermWeight_right (t : PairedTerm m p q) (i : Fin m) :
    pairedTermWeight t (slotRight i) =
      -memberInt t.1 i + memberInt t.2.1.val.1 i + memberInt t.2.2.val.1 i := by
  simp only [pairedTermWeight, Pi.add_apply, freePairWeight_right, pairChoiceWeight_right]

theorem pairedTermWeight_left (t : PairedTerm m p q) (i : Fin m) :
    pairedTermWeight t (slotLeft i) =
      memberInt t.1 i + memberInt t.2.1.val.2 i + memberInt t.2.2.val.2 i := by
  simp only [pairedTermWeight, Pi.add_apply, freePairWeight_left, pairChoiceWeight_left]

theorem local_pair_balance (f ae al be bl : Prop) [Decidable f] [Decidable ae]
    [Decidable al] [Decidable be] [Decidable bl] :
    (-(if f then (1 : ℤ) else 0)+(if ae then 1 else 0)+(if be then 1 else 0) = 1 ∧
      (if f then (1 : ℤ) else 0)+(if al then 1 else 0)+(if bl then 1 else 0) = 1) ↔
    ((f → ae) ∧ (al → ¬ f) ∧ (be ↔ ¬ (ae ∧ ¬ f)) ∧ (bl ↔ ¬ (al ∨ f))) := by
  by_cases hf : f <;> by_cases ha : ae <;> by_cases hl : al <;>
    by_cases hb : be <;> by_cases hc : bl <;> simp [hf,ha,hl,hb,hc]

theorem pairedTermWeight_eq_one_iff (hm : 0<m) (t : PairedTerm m p q) :
    pairedTermWeight t = (fun _ => 1) ↔ BalancedTerm t := by
  classical
  have hlocal (i : Fin m) :
      (pairedTermWeight t (slotRight i) = 1 ∧ pairedTermWeight t (slotLeft i) = 1) ↔
      ((i ∈ t.1 → i ∈ t.2.1.val.1) ∧ (i ∈ t.2.1.val.2 → i ∉ t.1) ∧
        (i ∈ t.2.2.val.1 ↔ ¬ (i ∈ t.2.1.val.1 ∧ i ∉ t.1)) ∧
        (i ∈ t.2.2.val.2 ↔ ¬ (i ∈ t.2.1.val.2 ∨ i ∈ t.1))) := by
    rw [pairedTermWeight_right, pairedTermWeight_left]
    exact local_pair_balance _ _ _ _ _
  constructor
  · intro h
    have hi (i : Fin m) := (hlocal i).mp
      ⟨congrFun h (slotRight i),congrFun h (slotLeft i)⟩
    refine ⟨fun i h => (hi i).1 h, Finset.disjoint_left.mpr (fun i h => (hi i).2.1 h), ?_, ?_⟩
    · ext i
      simpa only [Finset.mem_compl,Finset.mem_sdiff] using (hi i).2.2.1
    · ext i
      simpa only [Finset.mem_compl,Finset.mem_union] using (hi i).2.2.2
  · intro h
    have hi (i : Fin m) := (hlocal i).mpr
      ⟨fun hm => h.1 hm, fun hm => Finset.disjoint_left.mp h.2.1 hm,
        by simp only [h.2.2.1,Finset.mem_compl,Finset.mem_sdiff],
        by simp only [h.2.2.2,Finset.mem_compl,Finset.mem_union]⟩
    funext j
    obtain ⟨i, rfl⟩ := (slotSumEquiv hm).surjective j
    cases i with
    | inl i => exact (hi i).1
    | inr i => exact (hi i).2

end
end Schubert.RS.Family

