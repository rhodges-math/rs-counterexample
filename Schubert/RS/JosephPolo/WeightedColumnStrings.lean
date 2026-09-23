import Schubert.RS.JosephPolo.ColumnWeights

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance] Classical.propDecidable

theorem IsColumnWeightString.snoc_fixed {n d L : ℕ} {h : Fin (d+1) → Fin n}
    {i : AdjacentPosition n}
    {T : Fin (L+1) → (j : Fin d) → FlagMinorRowSet (h j.castSucc)}
    (hW : IsColumnWeightString i L (fun k => flagTupleWeight (fun j => h j.castSucc) (T k)))
    (C : FlagMinorRowSet (h (Fin.last d)))
    (hC : i.left ∈ C.val ↔ i.right ∈ C.val) :
    IsColumnWeightString i L (fun k => flagTupleWeight h (Fin.snoc (T k) C)) := by
  let c : Composition n := fun a => if a ∈ C.val then 1 else 0
  have hc : c i.left = c i.right := by simp only [c,hC]
  have he : (fun k => flagTupleWeight h (Fin.snoc (T k) C)) =
      (fun k a => flagTupleWeight (fun j => h j.castSucc) (T k) a + c a) := by
    funext k a
    exact flagTupleWeight_snoc h (T k) C a
  exact Eq.mpr (congrArg (IsColumnWeightString i L) he) (hW.add_fixed c hc)

theorem IsColumnWeightString.snoc_high {n d L : ℕ} {h : Fin (d+1) → Fin n}
    {i : AdjacentPosition n}
    {T : Fin (L+1) → (j : Fin d) → FlagMinorRowSet (h j.castSucc)}
    (hW : IsColumnWeightString i L (fun k => flagTupleWeight (fun j => h j.castSucc) (T k)))
    (C : FlagMinorRowSet (h (Fin.last d)))
    (ha : i.left ∈ C.val) (hb : i.right ∉ C.val) :
    IsColumnWeightString i (L+1) (fun k => flagTupleWeight h
      (Fin.cons (α := fun _ : Fin (L+2) => (j : Fin (d+1)) → FlagMinorRowSet (h j))
        (Fin.snoc (T 0) C)
        (fun k => Fin.snoc (T k) (C.permute (Equiv.swap i.left i.right))) k)) := by
  let c : Composition n := fun a => if a ∈ C.val then 1 else 0
  let e : Composition n := fun a => if a ∈ (C.permute (Equiv.swap i.left i.right)).val then 1 else 0
  have hca : c i.left = 1 := by simp [c,ha]
  have hcb : c i.right = 0 := by simp [c,hb]
  have hea : e i.left = 0 := by simp [e,FlagMinorRowSet.mem_permute,hb]
  have heb : e i.right = 1 := by simp [e,FlagMinorRowSet.mem_permute,ha]
  have hce : ∀ a, a ≠ i.left → a ≠ i.right → c a = e a := by
    intro a ha hb
    simp only [c,e,FlagMinorRowSet.mem_permute,Equiv.symm_swap,
      Equiv.swap_apply_of_ne_of_ne ha hb]
  have he : (fun k : Fin (L+2) => flagTupleWeight h
      (Fin.cons (α := fun _ : Fin (L+2) => (j : Fin (d+1)) → FlagMinorRowSet (h j))
        (Fin.snoc (T 0) C)
        (fun k => Fin.snoc (T k) (C.permute (Equiv.swap i.left i.right))) k)) =
      Fin.cons (fun a => flagTupleWeight (fun j => h j.castSucc) (T 0) a + c a)
        (fun k a => flagTupleWeight (fun j => h j.castSucc) (T k) a + e a) := by
    funext k
    refine Fin.cases ?_ (fun k => ?_) k
    · funext a
      exact flagTupleWeight_snoc h (T 0) C a
    · funext a
      exact flagTupleWeight_snoc h (T k) (C.permute (Equiv.swap i.left i.right)) a
  exact Eq.mpr (congrArg (IsColumnWeightString i (L+1)) he)
    (hW.add_high c e hca hcb hea heb hce)

theorem IsColumnWeightString.snoc_low {n d L : ℕ} {h : Fin (d+1) → Fin n}
    {i : AdjacentPosition n}
    {T : Fin (L+2) → (j : Fin d) → FlagMinorRowSet (h j.castSucc)}
    (hW : IsColumnWeightString i (L+1)
      (fun k => flagTupleWeight (fun j => h j.castSucc) (T k)))
    (C : FlagMinorRowSet (h (Fin.last d)))
    (ha : i.left ∈ C.val) (hb : i.right ∉ C.val) :
    IsColumnWeightString i L (fun k => flagTupleWeight h (Fin.snoc (T k.succ) C)) := by
  let c : Composition n := fun a => if a ∈ C.val then 1 else 0
  have hca : c i.left = 1 := by simp [c,ha]
  have hcb : c i.right = 0 := by simp [c,hb]
  have he : (fun k : Fin (L+1) => flagTupleWeight h (Fin.snoc (T k.succ) C)) =
      (fun k a => flagTupleWeight (fun j => h j.castSucc) (T k.succ) a + c a) := by
    funext k a
    exact flagTupleWeight_snoc h (T k.succ) C a
  exact Eq.mpr (congrArg (IsColumnWeightString i L) he) (hW.add_low c hca hcb)

theorem IsColumnWeightString.snoc_low_of_pos {n d L : ℕ} {h : Fin (d+1) → Fin n}
    {i : AdjacentPosition n}
    {T : Fin (L+1) → (j : Fin d) → FlagMinorRowSet (h j.castSucc)}
    (hW : IsColumnWeightString i L (fun k => flagTupleWeight (fun j => h j.castSucc) (T k)))
    (hL : 0 < L) (C : FlagMinorRowSet (h (Fin.last d)))
    (ha : i.left ∈ C.val) (hb : i.right ∉ C.val) :
    IsColumnWeightString i (L-1)
      (fun k => flagTupleWeight h (Fin.snoc (T ⟨k.val+1,by have := k.isLt; omega⟩) C)) := by
  cases L with
  | zero => omega
  | succ L => exact hW.snoc_low C ha hb

end
end Schubert.RS.Representation
