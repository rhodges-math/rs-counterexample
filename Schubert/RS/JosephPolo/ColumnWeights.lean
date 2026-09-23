import Schubert.RS.JosephPolo.ColumnPartition

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The exponent of a product of flag minors: count the appearances of
each row in the ordered tuple of columns. -/
def flagTupleWeight {n d : ℕ} (h : Fin d → Fin n)
    (T : (j : Fin d) → FlagMinorRowSet (h j)) : Composition n :=
  fun a => ∑ j, if a ∈ (T j).val then 1 else 0

theorem flagTupleWeight_snoc {n d : ℕ} (h : Fin (d+1) → Fin n)
    (T : (j : Fin d) → FlagMinorRowSet (h j.castSucc))
    (C : FlagMinorRowSet (h (Fin.last d))) (a : Fin n) :
    flagTupleWeight h (Fin.snoc T C) a =
      flagTupleWeight (fun j => h j.castSucc) T a + if a ∈ C.val then 1 else 0 := by
  unfold flagTupleWeight
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last]

/-- Natural-number coordinate equations for a string running down from
its highest weight. These equations avoid truncated subtraction. -/
structure IsColumnWeightString {n : ℕ} (i : AdjacentPosition n) (L : ℕ)
    (W : Fin (L+1) → Composition n) : Prop where
  head : W 0 i.left = W 0 i.right + L
  left : ∀ k, W k i.left + k.val = W 0 i.left
  right : ∀ k, W k i.right = W 0 i.right + k.val
  other : ∀ k a, a ≠ i.left → a ≠ i.right → W k a = W 0 a

theorem IsColumnWeightString.add_fixed {n L : ℕ} {i : AdjacentPosition n}
    {W : Fin (L+1) → Composition n} (hW : IsColumnWeightString i L W)
    (c : Composition n) (hc : c i.left = c i.right) :
    IsColumnWeightString i L (fun k a => W k a + c a) := by
  constructor
  · have := hW.head; omega
  · intro k; have := hW.left k; omega
  · intro k; have := hW.right k; omega
  · intro k a ha hb; rw [hW.other k a ha hb]

theorem IsColumnWeightString.add_high {n L : ℕ} {i : AdjacentPosition n}
    {W : Fin (L+1) → Composition n} (hW : IsColumnWeightString i L W)
    (c d : Composition n) (hca : c i.left = 1) (hcb : c i.right = 0)
    (hda : d i.left = 0) (hdb : d i.right = 1)
    (hcd : ∀ a, a ≠ i.left → a ≠ i.right → c a = d a) :
    IsColumnWeightString i (L+1)
      (Fin.cons (fun a => W 0 a + c a) (fun k a => W k a + d a)) := by
  constructor
  · simp only [Fin.cons_zero,hca,hcb,Nat.add_zero]
    have := hW.head
    omega
  · intro k
    refine Fin.cases ?_ (fun k => ?_) k
    · simp only [Fin.val_zero,Nat.add_zero]
    · simp only [Fin.cons_succ,Fin.cons_zero,Fin.val_succ,hca,hda,Nat.add_zero]
      have := hW.left k
      omega
  · intro k
    refine Fin.cases ?_ (fun k => ?_) k
    · simp only [Fin.val_zero,Nat.add_zero]
    · simp only [Fin.cons_succ,Fin.cons_zero,Fin.val_succ,hcb,hdb,Nat.add_zero]
      have := hW.right k
      omega
  · intro k a ha hb
    refine Fin.cases ?_ (fun k => ?_) k
    · rfl
    · simp only [Fin.cons_succ,Fin.cons_zero,hW.other k a ha hb,hcd a ha hb]

theorem IsColumnWeightString.add_low {n L : ℕ} {i : AdjacentPosition n}
    {W : Fin (L+2) → Composition n} (hW : IsColumnWeightString i (L+1) W)
    (c : Composition n) (hca : c i.left = 1) (hcb : c i.right = 0) :
    IsColumnWeightString i L (fun k a => W k.succ a + c a) := by
  constructor
  · change W (0 : Fin (L+1)).succ i.left + c i.left =
      W (0 : Fin (L+1)).succ i.right + c i.right + L
    have h0 := hW.head
    have ha := hW.left (0 : Fin (L+1)).succ
    have hb := hW.right (0 : Fin (L+1)).succ
    simp only [Fin.val_succ,Fin.val_zero,zero_add] at ha hb
    omega
  · intro k
    change W k.succ i.left + c i.left + k.val = W (0 : Fin (L+1)).succ i.left + c i.left
    have h0 := hW.left (0 : Fin (L+1)).succ
    have hk := hW.left k.succ
    simp only [Fin.val_succ,Fin.val_zero,zero_add] at h0 hk
    omega
  · intro k
    change W k.succ i.right + c i.right = W (0 : Fin (L+1)).succ i.right + c i.right + k.val
    have h0 := hW.right (0 : Fin (L+1)).succ
    have hk := hW.right k.succ
    simp only [Fin.val_succ,Fin.val_zero,zero_add] at h0 hk
    omega
  · intro k a ha hb
    change W k.succ a + c a = W (0 : Fin (L+1)).succ a + c a
    rw [hW.other k.succ a ha hb,hW.other (0 : Fin (L+1)).succ a ha hb]

end
end Schubert.RS.Representation
