import Schubert.RS.Family.Coordinates
import Schubert.RS.Family.Truncation

/-! Partition every nontrivial root factor into the two internal source
classes, paired targets, and the two source-to-target classes. -/

namespace Schubert.RS.Family
noncomputable section
open Representation

def targetEarly (P : Parameters) (i : Fin P.m) : Fin P.rank := target P (slotLeft i)
def targetLate (P : Parameters) (i : Fin P.m) : Fin P.rank := target P (slotRight i)

theorem targetEarly_value (P : Parameters) (i : Fin P.m) :
    (targetEarly P i).val=P.m+1+i.val := by simp [targetEarly,target,slotLeft]

theorem targetLate_value (P : Parameters) (i : Fin P.m) :
    (targetLate P i).val=4*P.m-1-i.val := by
  have hi:=i.isLt
  have hn : ¬(slotRight i).val<P.m := by
    simp only [slotRight,slotLeft,Fin.rev]
    omega
  change (if (slotRight i).val<P.m then P.m+1+(slotRight i).val
    else 2*P.m+(slotRight i).val)=_
  rw [if_neg hn]
  simp only [slotRight,slotLeft,Fin.rev]
  omega

theorem targetEarly_lt_late (P : Parameters) (i : Fin P.m) : targetEarly P i<targetLate P i := by
  have hi:=i.isLt
  change (targetEarly P i).val<(targetLate P i).val
  rw [targetEarly_value,targetLate_value]
  omega

abbrev SourceTargetA (P : Parameters) :=
  {s : Fin (2*P.p-1) × Slot P.m // sourceA P s.1<target P s.2}
abbrev SourceTargetB (P : Parameters) :=
  {s : Fin (2*P.q-1) × Slot P.m // sourceB P s.1<target P s.2}
abbrev GroupedRoot (P : Parameters) := PositiveRoot (2*P.p-1) ⊕
  (PositiveRoot (2*P.q-1) ⊕ (Fin P.m ⊕ (SourceTargetA P ⊕ SourceTargetB P)))

def groupedRoot (P : Parameters) : GroupedRoot P → PositiveRoot P.rank
  | .inl r => ⟨(sourceA P r.val.1,sourceA P r.val.2),sourceA_strictMono P r.property⟩
  | .inr (.inl r) => ⟨(sourceB P r.val.1,sourceB P r.val.2),sourceB_strictMono P r.property⟩
  | .inr (.inr (.inl i)) => ⟨(targetEarly P i,targetLate P i),targetEarly_lt_late P i⟩
  | .inr (.inr (.inr (.inl s))) => ⟨(sourceA P s.val.1,target P s.val.2),s.property⟩
  | .inr (.inr (.inr (.inr s))) => ⟨(sourceB P s.val.1,target P s.val.2),s.property⟩

theorem groupedRoot_injective (P : Parameters) : Function.Injective (groupedRoot P) := by
  intro x y h
  have h₁:=congrArg (fun r : PositiveRoot P.rank => r.val.1) h
  have h₂:=congrArg (fun r : PositiveRoot P.rank => r.val.2) h
  rcases x with x | x | x | x | x <;> rcases y with y | y | y | y | y <;>
    simp only [groupedRoot,targetEarly,targetLate] at h₁ h₂
  all_goals first
    | exact False.elim (sourceA_ne_B P _ _ h₁)
    | exact False.elim (sourceA_ne_B P _ _ h₁.symm)
    | exact False.elim (sourceA_ne_target P _ _ h₁)
    | exact False.elim (sourceA_ne_target P _ _ h₁.symm)
    | exact False.elim (sourceB_ne_target P _ _ h₁)
    | exact False.elim (sourceB_ne_target P _ _ h₁.symm)
    | exact False.elim (sourceA_ne_target P _ _ h₂)
    | exact False.elim (sourceA_ne_target P _ _ h₂.symm)
    | exact False.elim (sourceB_ne_target P _ _ h₂)
    | exact False.elim (sourceB_ne_target P _ _ h₂.symm)
    | skip
  all_goals simp only [Sum.inl.injEq,Sum.inr.injEq]
  all_goals first
    | exact slotLeft_injective ((target_strictMono P).injective h₁)
    | apply Subtype.ext
      apply Prod.ext
      · first | exact (sourceA_strictMono P).injective h₁ | exact (sourceB_strictMono P).injective h₁
      · first | exact (sourceA_strictMono P).injective h₂ | exact (sourceB_strictMono P).injective h₂
              | exact (target_strictMono P).injective h₂

theorem groupedRoot_relevant (P : Parameters) (s : GroupedRoot P) :
    coordinateClass P (groupedRoot P s).val.1=coordinateClass P (groupedRoot P s).val.2 ∨
      (sourceClass P (groupedRoot P s).val.1 ∧ ¬sourceClass P (groupedRoot P s).val.2) := by
  rcases s with r | r | i | s | s
  · left; apply Fin.ext; simp only [groupedRoot,sourceA_class]
  · left; apply Fin.ext; simp only [groupedRoot,sourceB_class]
  · left
    apply Fin.ext
    simp only [groupedRoot,targetEarly,targetLate,target_class,slotLeft,slotRight,Fin.rev]
    have hi:=i.isLt
    split_ifs <;> omega
  · right
    exact ⟨by change (coordinateClass P (sourceA P s.val.1)).val<2; rw [sourceA_class]; omega,
      target_not_source P s.val.2⟩
  · right
    exact ⟨by change (coordinateClass P (sourceB P s.val.1)).val<2; rw [sourceB_class]; omega,
      target_not_source P s.val.2⟩

theorem relevant_root_covered (P : Parameters) (r : PositiveRoot P.rank)
    (hr : coordinateClass P r.val.1=coordinateClass P r.val.2 ∨
      (sourceClass P r.val.1 ∧ ¬sourceClass P r.val.2)) : ∃ s,groupedRoot P s=r := by
  rcases r with ⟨⟨i,j⟩,hij⟩
  rcases coordinates_covered P i with ⟨x,rfl⟩ | ⟨x,rfl⟩ | ⟨x,rfl⟩ <;>
    rcases coordinates_covered P j with ⟨y,rfl⟩ | ⟨y,rfl⟩ | ⟨y,rfl⟩
  · exact ⟨.inl ⟨(x,y),(sourceA_strictMono P).lt_iff_lt.mp hij⟩,rfl⟩
  · rcases hr with h | h
    · have he:=congrArg Fin.val h
      simp only [sourceA_class,sourceB_class] at he
      omega
    · exact False.elim (h.2 (by change (coordinateClass P (sourceB P y)).val<2; rw [sourceB_class]; omega))
  · exact ⟨.inr (.inr (.inr (.inl ⟨(x,y),hij⟩))),rfl⟩
  · rcases hr with h | h
    · have he:=congrArg Fin.val h
      simp only [sourceA_class,sourceB_class] at he
      omega
    · exact False.elim (h.2 (by change (coordinateClass P (sourceA P y)).val<2; rw [sourceA_class]; omega))
  · exact ⟨.inr (.inl ⟨(x,y),(sourceB_strictMono P).lt_iff_lt.mp hij⟩),rfl⟩
  · exact ⟨.inr (.inr (.inr (.inr ⟨(x,y),hij⟩))),rfl⟩
  · exfalso
    rcases hr with h | h
    · apply target_not_source P x
      change (coordinateClass P (target P x)).val<2
      rw [h,sourceA_class]; omega
    · exact target_not_source P x h.1
  · exfalso
    rcases hr with h | h
    · apply target_not_source P x
      change (coordinateClass P (target P x)).val<2
      rw [h,sourceB_class]; omega
    · exact target_not_source P x h.1
  · have hxy : x<y := (target_strictMono P).lt_iff_lt.mp hij
    have hc : coordinateClass P (target P x)=coordinateClass P (target P y) :=
      hr.resolve_right (fun h => target_not_source P x h.1)
    rcases (target_pairing P x y).mp hc with he | he
    · exact False.elim ((ne_of_lt hxy) he)
    · have hx : x.val<P.m := by have hv : x.val<y.val:=hxy; omega
      refine ⟨.inr (.inr (.inl ⟨x.val,hx⟩)),?_⟩
      apply Subtype.ext
      apply Prod.ext
      · apply congrArg (target P)
        exact Fin.ext rfl
      · apply congrArg (target P)
        apply Fin.ext
        simp only [slotRight,slotLeft,Fin.rev]
        omega

theorem product_groupedRoot (P : Parameters) {R : Type*} [CommMonoid R]
    (f : PositiveRoot P.rank → R)
    (hf : ∀ r,¬(coordinateClass P r.val.1=coordinateClass P r.val.2 ∨
      (sourceClass P r.val.1 ∧ ¬sourceClass P r.val.2)) → f r=1) :
    (∏ r,f r)=∏ s : GroupedRoot P,f (groupedRoot P s) := by
  classical
  calc
    (∏ r,f r)=∏ r ∈ Finset.univ.image (groupedRoot P),f r := by
      symm
      apply Finset.prod_subset (Finset.subset_univ _)
      intro r _ hr
      apply hf
      intro h
      obtain ⟨s,hs⟩:=relevant_root_covered P r h
      exact hr (Finset.mem_image.mpr ⟨s,Finset.mem_univ _,hs⟩)
    _=∏ s : GroupedRoot P,f (groupedRoot P s) := Finset.prod_image (groupedRoot_injective P).injOn

end
end Schubert.RS.Family


