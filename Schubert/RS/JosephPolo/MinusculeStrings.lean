import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.EquivFin
import Lean.Elab.Tactic.Omega

namespace Schubert.RS.Representation

/-- Tensor a two-element string on the left of a string of length L.
The long string is (+,0),(-,0),...,(-,L); the short string is
(+,1),...,(+,L), and is empty when L=0. This is a finite bijection,
not an assumed crystal or module decomposition. -/
def minusculeTensorStringEquiv (L : ℕ) :
    Fin 2 × Fin (L+1) ≃ Fin (L+2) ⊕ Fin L where
  toFun x :=
    if x.1.val = 0 then
      if h : x.2.val = 0 then Sum.inl ⟨0,by omega⟩
      else Sum.inr ⟨x.2.val-1,by omega⟩
    else Sum.inl ⟨x.2.val+1,by omega⟩
  invFun x := match x with
    | Sum.inl k => if h : k.val = 0 then (0,0)
      else (1,⟨k.val-1,by omega⟩)
    | Sum.inr k => (0,⟨k.val+1,by omega⟩)
  left_inv x := by
    obtain ⟨a,b⟩ := x
    by_cases ha : a.val = 0
    · have ha' : a = 0 := Fin.ext ha
      subst a
      by_cases hb : b.val = 0
      · have hb' : b = 0 := Fin.ext hb
        subst b
        simp
      · simp only [Fin.val_zero,ite_true,dif_neg hb]
        apply Prod.ext
        · rfl
        · apply Fin.ext
          simp only [Fin.val_mk]
          omega
    · have ha' : a = 1 := Fin.ext (by have := a.isLt; omega)
      subst a
      simp only [Fin.val_one,one_ne_zero,ite_false,Fin.val_mk,Nat.add_eq_zero_iff,
        and_false,dif_neg]
      apply Prod.ext
      · rfl
      · apply Fin.ext
        simp
  right_inv x := by
    cases x with
    | inl k =>
      by_cases hk : k.val = 0
      · have hk' : k = 0 := Fin.ext hk
        subst k
        simp
      · simp only [dif_neg hk,Fin.val_one,one_ne_zero,ite_false,Fin.val_mk]
        apply congrArg Sum.inl
        apply Fin.ext
        simp only [Fin.val_mk]
        omega
    | inr k =>
      simp

end Schubert.RS.Representation
