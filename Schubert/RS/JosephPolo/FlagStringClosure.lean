import Schubert.RS.JosephPolo.FlagStringPartition

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance] Classical.propDecidable

theorem IsFlagDefiningString.snoc_low_of_pos {n d L : ℕ} {h : Fin (d+1) → Fin n}
    {i : AdjacentPosition n}
    {T : Fin (L+1) → (j : Fin d) → FlagMinorRowSet (h j.castSucc)}
    (hT : IsFlagDefiningString (fun j => h j.castSucc) i L T)
    (hL : 0 < L) (C : FlagMinorRowSet (h (Fin.last d)))
    (ha : i.left ∈ C.val) (hb : i.right ∉ C.val) :
    IsFlagDefiningString h i (L-1)
      (fun k => Fin.snoc (T ⟨k.val+1,by have := k.isLt; omega⟩) C) := by
  cases L with
  | zero => omega
  | succ L => exact hT.snoc_low C ha hb

theorem FiniteStringPartition.tensorColumn_good {n d : ℕ} {h : Fin (d+1) → Fin n}
    (i : AdjacentPosition n)
    (S : FiniteStringPartition ((j : Fin d) → FlagMinorRowSet (h j.castSucc)))
    (hS : ∀ a, IsFlagDefiningString (fun j => h j.castSucc) i (S.length a)
      (fun k => S.position ⟨a,k⟩))
    (a : ((S.tensorColumn i (h (Fin.last d))).map
      (Fin.snocEquiv (fun j => FlagMinorRowSet (h j)))).Index) :
    let R := (S.tensorColumn i (h (Fin.last d))).map
      (Fin.snocEquiv (fun j => FlagMinorRowSet (h j)))
    IsFlagDefiningString h i (R.length a) (fun k => R.position ⟨a,k⟩) := by
  rcases a with a | a
  · change IsFlagDefiningString h i (S.length a.2)
      (fun k => Fin.snoc (S.position ⟨a.2,k⟩) a.1.val)
    exact (hS a.2).snoc_fixed a.1.val a.1.property
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
      change IsFlagDefiningString h i (S.length a.2+1) _
      exact Eq.mpr (congrArg (IsFlagDefiningString h i (S.length a.2+1)) he)
        ((hS a.2).snoc_high a.1.val a.1.property.1 a.1.property.2)
    · change IsFlagDefiningString h i (S.length a.val.2-1) _
      have hgood := (hS a.val.2).snoc_low_of_pos a.property a.val.1.val
        a.val.1.property.1 a.val.1.property.2
      exact hgood

/-- All strings of the explicit tableau partition satisfy the four
defining-chain closure properties, in every rank and for arbitrary columns. -/
theorem flagStringPartition_good {n : ℕ} (i : AdjacentPosition n) (d : ℕ)
    (h : Fin d → Fin n) (a : (flagStringPartition i d h).Index) :
    IsFlagDefiningString h i ((flagStringPartition i d h).length a)
      (fun k => (flagStringPartition i d h).position ⟨a,k⟩) := by
  induction d with
  | zero =>
    constructor
    · intro w k l hkl _
      have hk := k.isLt
      have hl := l.isLt
      change k.val < 1 at hk
      change l.val < 1 at hl
      omega
    · intro w k l hkl hk _
      have hk' := k.isLt
      change k.val < 1 at hk'
      omega
    · intro w hw k l hkl _
      have hk := k.isLt
      have hl := l.isLt
      change k.val < 1 at hk
      change l.val < 1 at hl
      omega
    · intro w hw _
      exact emptyFlagDefiningChain _ _ _
  | succ d ih =>
    exact FiniteStringPartition.tensorColumn_good i
      (flagStringPartition i d (fun j => h j.castSucc)) (ih _) a

end
end Schubert.RS.Representation
