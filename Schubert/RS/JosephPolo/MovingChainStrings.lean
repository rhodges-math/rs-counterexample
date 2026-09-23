import Schubert.RS.JosephPolo.ChainStrings

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation

/-- The longer string in the tensor product with a moving column. -/
theorem IsFlagDefiningString.snoc_high {n d L : ℕ} {h : Fin (d+1) → Fin n}
    {i : AdjacentPosition n}
    {T : Fin (L+1) → (j : Fin d) → FlagMinorRowSet (h j.castSucc)}
    (hT : IsFlagDefiningString (fun j => h j.castSucc) i L T)
    (C : FlagMinorRowSet (h (Fin.last d)))
    (ha : i.left ∈ C.val) (hb : i.right ∉ C.val) :
    IsFlagDefiningString h i (L+1)
      (Fin.cons (Fin.snoc (T 0) C)
        (fun k => Fin.snoc (T k) (C.permute (Equiv.swap i.left i.right)))) := by
  let D := C.permute (Equiv.swap i.left i.right)
  have hDa : i.left ∉ D.val := by simpa [D,FlagMinorRowSet.mem_permute] using hb
  have hDb : i.right ∈ D.val := by simpa [D,FlagMinorRowSet.mem_permute] using ha
  have hD : D.permute (Equiv.swap i.left i.right) = C :=
    C.permute_swap_involutive _ _
  have asc (v : FinPermutation n) (hp : flagPrefixRows v (h (Fin.last d)) = C) :
      v.symm i.left < v.symm i.right :=
    flagColumn_inverse_ascent i _ v (by rwa [hp]) (by rwa [hp])
  have desc (v : FinPermutation n) (hp : flagPrefixRows v (h (Fin.last d)) = D) :
      v.symm i.right < v.symm i.left :=
    flagColumn_inverse_descent i _ v (by rwa [hp]) (by rwa [hp])
  constructor
  · intro w k l
    refine Fin.cases ?_ (fun k => ?_) k
    · intro hkl hchain
      have hl : l = (0 : Fin (L+1)).succ := Fin.ext (by simpa using hkl.symm)
      subst l
      simp only [Fin.cons_zero,Fin.cons_succ] at hchain ⊢
      obtain ⟨v,hv,hp,hchain⟩ := (hasFlagDefiningChain_snoc_iff h _ D w).mp hchain
      have hd := desc v hp
      have hp' : flagPrefixRows (v.leftAdjacentSwap i) (h (Fin.last d)) = C := by
        rw [flagPrefixRows_leftAdjacentSwap,hp,hD]
      exact (hasFlagDefiningChain_snoc_iff h _ C w).mpr
        ⟨v.leftAdjacentSwap i,strongBruhat_trans (left_reflection_le_of_descent i v hd) hv,
          hp',hT.head v hd hchain⟩
    · refine Fin.cases ?_ (fun l => ?_) l
      · intro hkl; have := k.isLt; simp only [Fin.val_succ,Fin.val_zero] at hkl; omega
      · intro hkl hchain
        simp only [Fin.cons_succ] at hchain ⊢
        obtain ⟨v,hv,hp,hchain⟩ := (hasFlagDefiningChain_snoc_iff h _ D w).mp hchain
        exact (hasFlagDefiningChain_snoc_iff h _ D w).mpr
          ⟨v,hv,hp,hT.raise v k l (by simpa using hkl) hchain⟩
  · intro w k l
    refine Fin.cases ?_ (fun k => ?_) k
    · intro _ hk; exact False.elim (Nat.not_lt_zero _ hk)
    · refine Fin.cases ?_ (fun l => ?_) l
      · intro hkl; simp only [Fin.val_succ,Fin.val_zero] at hkl; omega
      · intro hkl _ hchain
        simp only [Fin.cons_succ] at hchain ⊢
        obtain ⟨v,hv,hp,hchain⟩ := (hasFlagDefiningChain_snoc_iff h _ D w).mp hchain
        refine (hasFlagDefiningChain_snoc_iff h _ D w).mpr ⟨v,hv,hp,?_⟩
        by_cases hk : k.val = 0
        · exact hT.descent v (desc v hp) k l (by simpa using hkl) hchain
        · exact hT.forward v k l (by simpa using hkl) (Nat.pos_of_ne_zero hk) hchain
  · intro w hw k l
    refine Fin.cases ?_ (fun k => ?_) k
    · intro hkl hchain
      have hl : l = (0 : Fin (L+1)).succ := Fin.ext (by simpa using hkl.symm)
      subst l
      simp only [Fin.cons_zero,Fin.cons_succ] at hchain ⊢
      obtain ⟨v,hv,hp,hchain⟩ := (hasFlagDefiningChain_snoc_iff h _ C w).mp hchain
      have hv' := le_left_reflection_of_ascent i v (asc v hp)
      have hp' : flagPrefixRows (v.leftAdjacentSwap i) (h (Fin.last d)) = D := by
        rw [flagPrefixRows_leftAdjacentSwap,hp]
      exact (hasFlagDefiningChain_snoc_iff h _ D w).mpr
        ⟨v.leftAdjacentSwap i,left_reflected_lower_le_upper i hv (asc v hp) hw,
          hp',hchain.mono hv'⟩
    · refine Fin.cases ?_ (fun l => ?_) l
      · intro hkl; simp only [Fin.val_succ,Fin.val_zero] at hkl; omega
      · intro hkl hchain
        simp only [Fin.cons_succ] at hchain ⊢
        obtain ⟨v,hv,hp,hchain⟩ := (hasFlagDefiningChain_snoc_iff h _ D w).mp hchain
        exact (hasFlagDefiningChain_snoc_iff h _ D w).mpr
          ⟨v,hv,hp,hT.descent v (desc v hp) k l (by simpa using hkl) hchain⟩
  · intro w hw hchain
    simp only [Fin.cons_zero] at hchain ⊢
    obtain ⟨v,hv,hp,hchain⟩ := (hasFlagDefiningChain_snoc_iff h _ C w).mp hchain
    exact (hasFlagDefiningChain_snoc_iff h _ C _).mpr
      ⟨v,left_lower_le_reflected_upper i hv (asc v hp) hw,hp,hchain⟩

/-- The shorter string. Its old string has positive length, so this
construction does not introduce a spurious head when the short summand is empty. -/
theorem IsFlagDefiningString.snoc_low {n d L : ℕ} {h : Fin (d+1) → Fin n}
    {i : AdjacentPosition n}
    {T : Fin (L+2) → (j : Fin d) → FlagMinorRowSet (h j.castSucc)}
    (hT : IsFlagDefiningString (fun j => h j.castSucc) i (L+1) T)
    (C : FlagMinorRowSet (h (Fin.last d)))
    (ha : i.left ∈ C.val) (hb : i.right ∉ C.val) :
    IsFlagDefiningString h i L (fun k => Fin.snoc (T k.succ) C) := by
  constructor
  · intro w k l hkl hchain
    obtain ⟨v,hv,hp,hchain⟩ := (hasFlagDefiningChain_snoc_iff h _ C w).mp hchain
    exact (hasFlagDefiningChain_snoc_iff h _ C w).mpr
      ⟨v,hv,hp,hT.raise v k.succ l.succ (by simpa using hkl) hchain⟩
  · intro w k l hkl _ hchain
    obtain ⟨v,hv,hp,hchain⟩ := (hasFlagDefiningChain_snoc_iff h _ C w).mp hchain
    exact (hasFlagDefiningChain_snoc_iff h _ C w).mpr
      ⟨v,hv,hp,hT.forward v k.succ l.succ (by simpa using hkl) (Nat.succ_pos _) hchain⟩
  · intro w _ k l hkl hchain
    obtain ⟨v,hv,hp,hchain⟩ := (hasFlagDefiningChain_snoc_iff h _ C w).mp hchain
    exact (hasFlagDefiningChain_snoc_iff h _ C w).mpr
      ⟨v,hv,hp,hT.forward v k.succ l.succ (by simpa using hkl) (Nat.succ_pos _) hchain⟩
  · intro w hw hchain
    obtain ⟨v,hv,hp,hchain⟩ := (hasFlagDefiningChain_snoc_iff h _ C w).mp hchain
    have hv' := flagColumn_inverse_ascent i (h (Fin.last d)) v
      (by rwa [hp]) (by rwa [hp])
    exact (hasFlagDefiningChain_snoc_iff h _ C _).mpr
      ⟨v,left_lower_le_reflected_upper i hv hv' hw,hp,hchain⟩

end
end Schubert.RS.Representation
