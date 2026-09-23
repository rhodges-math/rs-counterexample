import Schubert.RS.JosephPolo.FlagStringClosure

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation

private theorem fin_forward_interval {N : ℕ} (P : Fin N → Prop) (k l : Fin N)
    (hkl : k.val ≤ l.val)
    (step : ∀ a b : Fin N, a.val+1=b.val → k.val ≤ a.val → P a → P b)
    (hk : P k) : P l := by
  have aux : ∀ m (hm : m < N), k.val ≤ m → P ⟨m,hm⟩ := by
    intro m
    induction m with
    | zero =>
      intro hm hkm
      have he : k = ⟨0,hm⟩ := Fin.ext (by change k.val = 0; omega)
      rwa [← he]
    | succ m ih =>
      intro hm hkm
      by_cases he : k.val = m+1
      · have hek : k = ⟨m+1,hm⟩ := Fin.ext he
        rwa [← hek]
      · have hkm' : k.val ≤ m := by omega
        have hm' : m < N := by omega
        exact step ⟨m,hm'⟩ ⟨m+1,hm⟩ rfl hkm' (ih hm' hkm')
  exact aux l.val l.isLt hkl

private theorem fin_backward_interval {N : ℕ} (P : Fin N → Prop) (k l : Fin N)
    (hkl : k.val ≤ l.val)
    (step : ∀ a b : Fin N, a.val+1=b.val → P b → P a)
    (hl : P l) : P k := by
  have aux : ∀ m (hm : m < N), ∀ k : Fin N, k.val ≤ m → P ⟨m,hm⟩ → P k := by
    intro m
    induction m with
    | zero =>
      intro hm k hkm hP
      have he : k = ⟨0,hm⟩ := Fin.ext (by change k.val = 0; omega)
      rwa [he]
    | succ m ih =>
      intro hm k hkm hP
      by_cases he : k.val = m+1
      · have hek : k = ⟨m+1,hm⟩ := Fin.ext he
        rwa [hek]
      · have hkm' : k.val ≤ m := by omega
        have hm' : m < N := by omega
        exact ih hm' k hkm' (step ⟨m,hm'⟩ ⟨m+1,hm⟩ rfl hP)
  exact aux l.val l.isLt k hkl hl

theorem IsFlagDefiningString.raise_le {n d L : ℕ} {h : Fin d → Fin n}
    {i : AdjacentPosition n} {T : Fin (L+1) → (j : Fin d) → FlagMinorRowSet (h j)}
    (hT : IsFlagDefiningString h i L T) (w : FinPermutation n)
    (k l : Fin (L+1)) (hkl : k.val ≤ l.val) (hl : HasFlagDefiningChain h (T l) w) :
    HasFlagDefiningChain h (T k) w :=
  fin_backward_interval _ k l hkl (hT.raise w) hl

theorem IsFlagDefiningString.full_of_nonhead {n d L : ℕ} {h : Fin d → Fin n}
    {i : AdjacentPosition n} {T : Fin (L+1) → (j : Fin d) → FlagMinorRowSet (h j)}
    (hT : IsFlagDefiningString h i L T) (w : FinPermutation n)
    (k : Fin (L+1)) (hk : 0<k.val) (hchain : HasFlagDefiningChain h (T k) w) :
    ∀ l, HasFlagDefiningChain h (T l) w := by
  intro l
  rcases le_total l.val k.val with hl | hl
  · exact hT.raise_le w l k hl hchain
  · exact fin_forward_interval _ k l hl
      (fun a b hab hka => hT.forward w a b hab (lt_of_lt_of_le hk hka)) hchain

/-- A Bruhat bound selects no entries, only the head, or the whole string. -/
theorem IsFlagDefiningString.trichotomy {n d L : ℕ} {h : Fin d → Fin n}
    {i : AdjacentPosition n} {T : Fin (L+1) → (j : Fin d) → FlagMinorRowSet (h j)}
    (hT : IsFlagDefiningString h i L T) (w : FinPermutation n) :
    (∀ k, ¬ HasFlagDefiningChain h (T k) w) ∨
    (∀ k, HasFlagDefiningChain h (T k) w ↔ k=0) ∨
    (∀ k, HasFlagDefiningChain h (T k) w) := by
  classical
  by_cases hhead : HasFlagDefiningChain h (T 0) w
  · by_cases hnon : ∃ k, 0<k.val ∧ HasFlagDefiningChain h (T k) w
    · obtain ⟨k,hk,hchain⟩ := hnon
      exact Or.inr (Or.inr (hT.full_of_nonhead w k hk hchain))
    · refine Or.inr (Or.inl (fun k => ⟨?_,?_⟩))
      · intro hchain
        apply Fin.ext
        by_contra hk
        exact hnon ⟨k,Nat.pos_of_ne_zero hk,hchain⟩
      · intro hk; simpa only [hk] using hhead
  · exact Or.inl (fun k hk => hhead (hT.raise_le w 0 k (Nat.zero_le _) hk))

/-- At an inverse descent, admissibility at any position is equivalent
to admissibility of the head below the reflected permutation. -/
theorem IsFlagDefiningString.descent_iff_head {n d L : ℕ} {h : Fin d → Fin n}
    {i : AdjacentPosition n} {T : Fin (L+1) → (j : Fin d) → FlagMinorRowSet (h j)}
    (hT : IsFlagDefiningString h i L T) (w : FinPermutation n)
    (hw : w.symm i.right < w.symm i.left) (k : Fin (L+1)) :
    HasFlagDefiningChain h (T k) w ↔
      HasFlagDefiningChain h (T 0) (w.leftAdjacentSwap i) := by
  constructor
  · intro hk
    exact hT.head w hw (hT.raise_le w 0 k (Nat.zero_le _) hk)
  · intro hh
    have hh' := hh.mono (left_reflection_le_of_descent i w hw)
    exact fin_forward_interval _ 0 k (Nat.zero_le _)
      (fun a b hab _ => hT.descent w hw a b hab) hh'

end
end Schubert.RS.Representation
