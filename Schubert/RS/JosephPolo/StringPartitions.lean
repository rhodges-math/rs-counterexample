import Schubert.RS.JosephPolo.MinusculeStrings

namespace Schubert.RS.Representation

/-- Heads after tensoring with fixed columns and two-element moving columns.
The short head is present only when the old length is positive. -/
abbrev TensorStringHead (Z P I : Type) (L : I → ℕ) :=
  (Z × I) ⊕ (P × I) ⊕ {a : P × I // 0 < L a.2}

def tensorStringLength {Z P I : Type} (L : I → ℕ) : TensorStringHead Z P I L → ℕ
  | Sum.inl a => L a.2
  | Sum.inr (Sum.inl a) => L a.2 + 1
  | Sum.inr (Sum.inr a) => L a.val.2 - 1

/-- An explicit partition of a tensor product into nonempty strings. -/
def tensorStringPositions {Z P I : Type} (L : I → ℕ) :
    (Σ a : TensorStringHead Z P I L, Fin (tensorStringLength L a + 1)) ≃
      (Z ⊕ (P × Fin 2)) × (Σ a : I, Fin (L a + 1)) where
  toFun x := match x with
    | ⟨Sum.inl a,k⟩ => (Sum.inl a.1,⟨a.2,k⟩)
    | ⟨Sum.inr (Sum.inl a),k⟩ =>
      let b := (minusculeTensorStringEquiv (L a.2)).symm (Sum.inl k)
      (Sum.inr (a.1,b.1),⟨a.2,b.2⟩)
    | ⟨Sum.inr (Sum.inr a),k⟩ =>
      let k' : Fin (L a.val.2) := ⟨k.val,by
        have := a.property
        have hk : k.val < L a.val.2 - 1 + 1 := k.isLt
        omega⟩
      let b := (minusculeTensorStringEquiv (L a.val.2)).symm (Sum.inr k')
      (Sum.inr (a.val.1,b.1),⟨a.val.2,b.2⟩)
  invFun x := match x with
    | (Sum.inl z,⟨a,k⟩) => ⟨Sum.inl (z,a),k⟩
    | (Sum.inr (p,b),⟨a,k⟩) =>
      match (minusculeTensorStringEquiv (L a)) (b,k) with
      | Sum.inl j => ⟨Sum.inr (Sum.inl (p,a)),j⟩
      | Sum.inr j =>
        ⟨Sum.inr (Sum.inr ⟨(p,a),Nat.zero_lt_of_lt j.isLt⟩),
          ⟨j.val,by change j.val < L a - 1 + 1; have := j.isLt; omega⟩⟩
  left_inv x := by
    obtain ⟨a,k⟩ := x
    rcases a with a | a
    · rfl
    · rcases a with a | a
      · simp only [Prod.mk.eta,Equiv.apply_symm_apply]
      · simp only [Prod.mk.eta,Equiv.apply_symm_apply]
  right_inv x := by
    obtain ⟨c,a,k⟩ := x
    rcases c with z | ⟨p,b⟩
    · rfl
    · generalize he : (minusculeTensorStringEquiv (L a)) (b,k) = j
      have hb := (minusculeTensorStringEquiv (L a)).symm_apply_eq.mpr he.symm
      cases j with
      | inl j =>
        simp only [he,hb]
      | inr j =>
        simp only [he,hb]

end Schubert.RS.Representation
