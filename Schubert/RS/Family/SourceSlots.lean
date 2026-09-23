import Schubert.RS.Family.Coordinates

/-! Every source-to-target root is an available slot of its flagged row.
The reindexing is independent of the family and permits unequal source sizes. -/

namespace Schubert.RS.Family
noncomputable section
variable {d M n : ℕ}

abbrev AvailableSlot (y : Fin d → Fin (M+1)) := Σ i : Fin d,Fin ((y i.rev).val+1)

def availableSlotIndex (y : Fin d → Fin (M+1)) (i : Fin d)
    (h : Fin ((y i.rev).val+1)) : Fin (M+1) :=
  ⟨h.val,by have hheight:=(y i.rev).isLt; have hh:=h.isLt; omega⟩

def sourceTargetSlotEquiv (y : Fin d → Fin (M+1))
    (source : Fin d → Fin n) (target : Fin (M+1) → Fin n)
    (hs : ∀ i j,source i<target j ↔ j.rev.val≤(y i.rev).val) :
    AvailableSlot y ≃ {p : Fin d × Fin (M+1) // source p.1<target p.2} where
  toFun p:=⟨(p.1,(availableSlotIndex y p.1 p.2).rev),by
    apply (hs _ _).mpr
    simpa only [Fin.rev_rev,availableSlotIndex] using Nat.le_of_lt_succ p.2.isLt⟩
  invFun p:=⟨p.val.1,⟨p.val.2.rev.val,Nat.lt_succ_of_le ((hs _ _).mp p.property)⟩⟩
  left_inv p:=by
    rcases p with ⟨i,h⟩
    simp only [Fin.rev_rev]
    rfl
  right_inv p:=by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change (availableSlotIndex y p.val.1 ⟨p.val.2.rev.val,_⟩).rev=p.val.2
      have he : availableSlotIndex y p.val.1
          ⟨p.val.2.rev.val,Nat.lt_succ_of_le ((hs _ _).mp p.property)⟩=p.val.2.rev := Fin.ext rfl
      rw [he,Fin.rev_rev]

theorem source_target_slot_product {R : Type*} [CommMonoid R]
    (y : Fin d → Fin (M+1)) (source : Fin d → Fin n) (target : Fin (M+1) → Fin n)
    (hs : ∀ i j,source i<target j ↔ j.rev.val≤(y i.rev).val) (f : Fin d → Fin (M+1) → R) :
    (∏ p : {p : Fin d × Fin (M+1) // source p.1<target p.2},f p.val.1 p.val.2.rev)=
      ∏ i,∏ h : Fin ((y i.rev).val+1),f i (availableSlotIndex y i h) := by
  classical
  rw [← Equiv.prod_comp (sourceTargetSlotEquiv y source target hs) (fun p => f p.val.1 p.val.2.rev)]
  change (∏ p : AvailableSlot y,f p.1 (availableSlotIndex y p.1 p.2).rev.rev)=_
  simp only [Fin.rev_rev]
  exact Fintype.prod_sigma _

end
end Schubert.RS.Family
