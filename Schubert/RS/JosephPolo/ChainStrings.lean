import Schubert.RS.JosephPolo.DefiningChains
import Schubert.RS.JosephPolo.ColumnReflections
import Schubert.RS.JosephPolo.MinusculeStrings

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation

theorem hasFlagDefiningChain_snoc_iff {n d : ℕ} (h : Fin (d+1) → Fin n)
    (T : (j : Fin d) → FlagMinorRowSet (h j.castSucc))
    (C : FlagMinorRowSet (h (Fin.last d))) (w : FinPermutation n) :
    HasFlagDefiningChain h (Fin.snoc T C) w ↔
      ∃ v : FinPermutation n, v ≤ᴮ w ∧ flagPrefixRows v (h (Fin.last d)) = C ∧
        HasFlagDefiningChain (fun j => h j.castSucc) T v := by
  simpa using (hasFlagDefiningChain_iff_last (h:=h) (T:=Fin.snoc T C) (w:=w))

theorem flagColumn_inverse_ascent {n : ℕ} (i : AdjacentPosition n)
    (k : Fin n) (w : FinPermutation n)
    (ha : i.left ∈ (flagPrefixRows w k).val)
    (hb : i.right ∉ (flagPrefixRows w k).val) :
    w.symm i.left < w.symm i.right := by
  rw [mem_flagPrefixRows] at ha hb
  exact lt_of_le_of_lt ha (lt_of_not_ge hb)

theorem flagColumn_inverse_descent {n : ℕ} (i : AdjacentPosition n)
    (k : Fin n) (w : FinPermutation n)
    (ha : i.left ∉ (flagPrefixRows w k).val)
    (hb : i.right ∈ (flagPrefixRows w k).val) :
    w.symm i.right < w.symm i.left := by
  rw [mem_flagPrefixRows] at ha hb
  exact lt_of_le_of_lt hb (lt_of_not_ge ha)

theorem flagPrefixRows_leftAdjacentSwap {n : ℕ} (w : FinPermutation n)
    (i : AdjacentPosition n) (k : Fin n) :
    flagPrefixRows (w.leftAdjacentSwap i) k =
      (flagPrefixRows w k).permute (Equiv.swap i.left i.right) :=
  flagPrefixRows_mul (Equiv.swap i.left i.right) w k

theorem FlagMinorRowSet.permute_swap_involutive {n : ℕ} {k : Fin n}
    (C : FlagMinorRowSet k) (a b : Fin n) :
    (C.permute (Equiv.swap a b)).permute (Equiv.swap a b) = C := by
  classical
  apply Subtype.ext
  ext j
  simp only [FlagMinorRowSet.mem_permute,Equiv.symm_swap,Equiv.swap_apply_self]

/-- The four defining-chain closure properties of an exhibited finite string.
No character formula, independence assertion, or representation is assumed. -/
structure IsFlagDefiningString {n d : ℕ} (h : Fin d → Fin n)
    (i : AdjacentPosition n) (L : ℕ)
    (T : Fin (L+1) → (j : Fin d) → FlagMinorRowSet (h j)) : Prop where
  raise : ∀ (w : FinPermutation n) (k l : Fin (L+1)), k.val+1=l.val →
    HasFlagDefiningChain h (T l) w → HasFlagDefiningChain h (T k) w
  forward : ∀ (w : FinPermutation n) (k l : Fin (L+1)), k.val+1=l.val → 0<k.val →
    HasFlagDefiningChain h (T k) w → HasFlagDefiningChain h (T l) w
  descent : ∀ (w : FinPermutation n), w.symm i.right < w.symm i.left →
    ∀ (k l : Fin (L+1)), k.val+1=l.val →
    HasFlagDefiningChain h (T k) w → HasFlagDefiningChain h (T l) w
  head : ∀ (w : FinPermutation n), w.symm i.right < w.symm i.left →
    HasFlagDefiningChain h (T 0) w → HasFlagDefiningChain h (T 0) (w.leftAdjacentSwap i)

/-- A column fixed by the adjacent reflection leaves the string length unchanged. -/
theorem IsFlagDefiningString.snoc_fixed {n d L : ℕ} {h : Fin (d+1) → Fin n}
    {i : AdjacentPosition n}
    {T : Fin (L+1) → (j : Fin d) → FlagMinorRowSet (h j.castSucc)}
    (hT : IsFlagDefiningString (fun j => h j.castSucc) i L T)
    (C : FlagMinorRowSet (h (Fin.last d)))
    (hC : i.left ∈ C.val ↔ i.right ∈ C.val) :
    IsFlagDefiningString h i L (fun k => Fin.snoc (T k) C) := by
  have hfix := C.permute_swap_eq_self i.left i.right hC
  constructor
  · intro w k l hkl hchain
    obtain ⟨v,hv,hp,hchain⟩ := (hasFlagDefiningChain_snoc_iff h _ C w).mp hchain
    exact (hasFlagDefiningChain_snoc_iff h _ C w).mpr
      ⟨v,hv,hp,hT.raise v k l hkl hchain⟩
  · intro w k l hkl hk hchain
    obtain ⟨v,hv,hp,hchain⟩ := (hasFlagDefiningChain_snoc_iff h _ C w).mp hchain
    exact (hasFlagDefiningChain_snoc_iff h _ C w).mpr
      ⟨v,hv,hp,hT.forward v k l hkl hk hchain⟩
  · intro w hw k l hkl hchain
    obtain ⟨v,hv,hp,hchain⟩ := (hasFlagDefiningChain_snoc_iff h _ C w).mp hchain
    have hcol : i.right ∈ (flagPrefixRows v (h (Fin.last d))).val →
        i.left ∈ (flagPrefixRows v (h (Fin.last d))).val := by
      simpa only [hp] using hC.mpr
    obtain ⟨v',hvv',hv'w,hp',hd⟩ := flagColumn_lift_up i _ hv hw hcol
    have hp'C : flagPrefixRows v' (h (Fin.last d)) = C := by
      simpa only [hp,hfix] using hp'
    exact (hasFlagDefiningChain_snoc_iff h _ C w).mpr
      ⟨v',hv'w,hp'C,hT.descent v' hd k l hkl (hchain.mono hvv')⟩
  · intro w hw hchain
    obtain ⟨v,hv,hp,hchain⟩ := (hasFlagDefiningChain_snoc_iff h _ C w).mp hchain
    rcases lt_or_gt_of_ne (v.symm.injective.ne i.left_ne_right) with ha | hd
    · exact (hasFlagDefiningChain_snoc_iff h _ C _).mpr
        ⟨v,left_lower_le_reflected_upper i hv ha hw,hp,hchain⟩
    · have hp' : flagPrefixRows (v.leftAdjacentSwap i) (h (Fin.last d)) = C := by
        rw [flagPrefixRows_leftAdjacentSwap,hp,hfix]
      exact (hasFlagDefiningChain_snoc_iff h _ C _).mpr
        ⟨v.leftAdjacentSwap i,left_reflections_le_of_both_descent i hv hd hw,
          hp',hT.head v hd hchain⟩

end
end Schubert.RS.Representation
