import Schubert.RS.Family.SourceSelections
import Mathlib.Data.Finset.Sum

/-! Reversed target slots. The successor form of the ambient size matches
the Hall determinant formula. For m>0 it is exactly 2m. -/

namespace Schubert.RS.Family
noncomputable section
variable {m : ℕ}

abbrev Slot (m : ℕ) := Fin (2*m-1+1)

def slotLeft (i : Fin m) : Slot m := ⟨i.val,by have h:=i.isLt; omega⟩
def slotRight (i : Fin m) : Slot m := (slotLeft i).rev

theorem slotLeft_injective : Function.Injective (slotLeft (m:=m)) := by
  intro i j h
  exact Fin.ext (congrArg (fun z : Slot m => z.val) h)

theorem slotRight_injective : Function.Injective (slotRight (m:=m)) :=
  Fin.rev_injective.comp slotLeft_injective

theorem slots_ne (i j : Fin m) : slotLeft i ≠ slotRight j := by
  have hi:=i.isLt
  have hj:=j.isLt
  intro h
  have he := congrArg (fun z : Slot m => z.val) h
  simp only [slotRight,slotLeft,Fin.rev] at he
  omega

def slotSum : Fin m ⊕ Fin m → Slot m := Sum.elim slotRight slotLeft

theorem slotSum_bijective (hm : 0<m) : Function.Bijective (slotSum (m:=m)) := by
  constructor
  · intro i j h
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (slotRight_injective h)
      | inr j => exact False.elim (slots_ne j i h.symm)
    | inr i =>
      cases j with
      | inl j => exact False.elim (slots_ne i j h)
      | inr j => exact congrArg Sum.inr (slotLeft_injective h)
  · intro j
    have hj:=j.isLt
    by_cases h : j.val<m
    · exact ⟨Sum.inr ⟨j.val,h⟩,Fin.ext rfl⟩
    · refine ⟨Sum.inl ⟨2*m-1-j.val,by omega⟩,?_⟩
      apply Fin.ext
      simp only [slotSum,Sum.elim_inl,slotRight,slotLeft,Fin.rev]
      omega

def slotSumEquiv (hm : 0<m) : Fin m ⊕ Fin m ≃ Slot m :=
  Equiv.ofBijective slotSum (slotSum_bijective hm)

def pairSlots (hm : 0<m) : (Finset (Fin m) × Finset (Fin m)) ≃ Finset (Slot m) :=
  Finset.sumEquiv.toEquiv.symm.trans (slotSumEquiv hm).finsetCongr

theorem pairSlots_apply (hm : 0<m) (s : Finset (Fin m) × Finset (Fin m)) :
    pairSlots hm s=(s.1.disjSum s.2).map (slotSumEquiv hm).toEmbedding := rfl

theorem pairSlots_card (hm : 0<m) (s : Finset (Fin m) × Finset (Fin m)) :
    (pairSlots hm s).card=s.1.card+s.2.card := by
  rw [pairSlots_apply,Finset.card_map,Finset.card_disjSum]

theorem slotSum_low (hm : 0<m) (j : Fin m ⊕ Fin m) :
    ((slotSumEquiv hm) j).val<m ↔ j.isRight := by
  cases j <;> simp [slotSumEquiv,slotSum,slotRight,slotLeft,Fin.rev] <;> omega

theorem pairSlots_low_card (hm : 0<m) (s : Finset (Fin m) × Finset (Fin m)) :
    ((pairSlots hm s).filter (fun j => j.val<m)).card=s.2.card := by
  rw [pairSlots_apply,Finset.filter_map]
  have he : (s.1.disjSum s.2).filter (fun j => ((slotSumEquiv hm) j).val<m)=
      (∅ : Finset (Fin m)).disjSum s.2 := by
    ext j
    cases j <;> simp [slotSum_low]
  change ((s.1.disjSum s.2).filter (fun j => ((slotSumEquiv hm) j).val<m) |>.map
    (slotSumEquiv hm).toEmbedding).card=_
  rw [he,Finset.card_map,Finset.card_disjSum,Finset.card_empty,zero_add]

end
end Schubert.RS.Family


