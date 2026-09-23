import Schubert.RS.JosephPolo.FlagStringPartition
import Schubert.RS.JosephPolo.WeightedColumnStrings

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance] Classical.propDecidable

theorem FiniteStringPartition.tensorColumn_weight {n d : ℕ} {h : Fin (d+1) → Fin n}
    (i : AdjacentPosition n)
    (S : FiniteStringPartition ((j : Fin d) → FlagMinorRowSet (h j.castSucc)))
    (hS : ∀ a, IsColumnWeightString i (S.length a)
      (fun k => flagTupleWeight (fun j => h j.castSucc) (S.position ⟨a,k⟩)))
    (a : ((S.tensorColumn i (h (Fin.last d))).map
      (Fin.snocEquiv (fun j => FlagMinorRowSet (h j)))).Index) :
    let R := (S.tensorColumn i (h (Fin.last d))).map
      (Fin.snocEquiv (fun j => FlagMinorRowSet (h j)))
    IsColumnWeightString i (R.length a) (fun k => flagTupleWeight h (R.position ⟨a,k⟩)) := by
  rcases a with a | a
  · exact (hS a.2).snoc_fixed a.1.val a.1.property
  · rcases a with a | a
    · have he :
          (fun k : Fin (S.length a.2+2) => (((S.tensorColumn i (h (Fin.last d))).map
            (Fin.snocEquiv (fun j => FlagMinorRowSet (h j))))).position
              ⟨Sum.inr (Sum.inl a),k⟩) =
          Fin.cons (Fin.snoc (S.position ⟨a.2,0⟩) a.1.val)
            (fun k => Fin.snoc (S.position ⟨a.2,k⟩)
              (a.1.val.permute (Equiv.swap i.left i.right))) := by
        funext k
        refine Fin.cases ?_ (fun k => ?_) k
        · rfl
        · change Fin.snoc (α := fun j : Fin (d+1) => FlagMinorRowSet (h j))
            (S.position ⟨a.2,((minusculeTensorStringEquiv (S.length a.2)).symm
              (Sum.inl k.succ)).2⟩)
            ((flagColumnPartition i (h (Fin.last d))).symm (Sum.inr
              (a.1,((minusculeTensorStringEquiv (S.length a.2)).symm (Sum.inl k.succ)).1))) = _
          simp [minusculeTensorStringEquiv,flagColumnPartition]
      change IsColumnWeightString i (S.length a.2+1) _
      exact Eq.mpr (congrArg (fun f : Fin (S.length a.2+2) → (j : Fin (d+1)) → FlagMinorRowSet (h j) =>
        IsColumnWeightString i (S.length a.2+1)
        (fun k => flagTupleWeight h (f k))) he)
        ((hS a.2).snoc_high a.1.val a.1.property.1 a.1.property.2)
    · exact (hS a.val.2).snoc_low_of_pos a.property a.val.1.val
        a.val.1.property.1 a.val.1.property.2

theorem flagTupleWeight_empty {n : ℕ} (h : Fin 0 → Fin n)
    (T : (j : Fin 0) → FlagMinorRowSet (h j)) : flagTupleWeight h T = 0 := by
  funext a
  simp [flagTupleWeight]

/-- The explicit tableau partition has the ordinary rank-one string weights. -/
theorem flagStringPartition_weight {n : ℕ} (i : AdjacentPosition n) (d : ℕ)
    (h : Fin d → Fin n) (a : (flagStringPartition i d h).Index) :
    IsColumnWeightString i ((flagStringPartition i d h).length a)
      (fun k => flagTupleWeight h ((flagStringPartition i d h).position ⟨a,k⟩)) := by
  induction d with
  | zero =>
    change IsColumnWeightString i 0 _
    constructor
    · simp only [flagTupleWeight_empty,Pi.zero_apply,Nat.add_zero]
    · intro k
      simp only [flagTupleWeight_empty,Pi.zero_apply,Nat.zero_add]
      have hk : k.val < 1 := k.isLt
      omega
    · intro k
      simp only [flagTupleWeight_empty,Pi.zero_apply,Nat.zero_add]
      have hk : k.val < 1 := k.isLt
      omega
    · intro k a ha hb
      simp only [flagTupleWeight_empty,Pi.zero_apply]
  | succ d ih =>
    exact FiniteStringPartition.tensorColumn_weight i
      (flagStringPartition i d (fun j => h j.castSucc)) (ih _) a

end
end Schubert.RS.Representation
