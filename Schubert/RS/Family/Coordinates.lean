import Schubert.RS.Family.Data
import Schubert.RS.Family.HallChoices

/-! Source embeddings and the two oppositely ordered target blocks. These
are symbolic descriptions of every coordinate, including empty middle blocks. -/

namespace Schubert.RS.Family

def sourceA (P : Parameters) (i : Fin (2*P.p-1)) : Fin P.rank :=
  ⟨if i.val<P.p then i.val else 2*P.m+1+(i.val-P.p),by
    have hi:=i.isLt
    have hp:=P.p_pos
    have hpm:=P.p_le_m
    change _<4*P.m
    split_ifs <;> omega⟩

def sourceB (P : Parameters) (i : Fin (2*P.q-1)) : Fin P.rank :=
  ⟨if i.val<P.q then P.p+i.val else 2*P.m+P.p+(i.val-P.q),by
    have hi:=i.isLt
    have hp:=P.p_pos
    have hq:=P.q_pos
    have he:=P.pq_eq
    change _<4*P.m
    split_ifs <;> omega⟩

def target (P : Parameters) (i : Slot P.m) : Fin P.rank :=
  ⟨if i.val<P.m then P.m+1+i.val else 2*P.m+i.val,by
    have hi:=i.isLt
    have hm:=P.m_pos
    change _<4*P.m
    split_ifs <;> omega⟩

theorem sourceA_strictMono (P : Parameters) : StrictMono (sourceA P) := by
  intro i j hij
  have hi:=i.isLt
  have hj:=j.isLt
  have he : i.val<j.val := hij
  have hp:=P.p_le_m
  change (sourceA P i).val<(sourceA P j).val
  simp only [sourceA]
  split_ifs <;> omega

theorem sourceB_strictMono (P : Parameters) : StrictMono (sourceB P) := by
  intro i j hij
  have hi:=i.isLt
  have hj:=j.isLt
  have he : i.val<j.val := hij
  have hq:=P.q_le_m
  change (sourceB P i).val<(sourceB P j).val
  simp only [sourceB]
  split_ifs <;> omega

theorem target_strictMono (P : Parameters) : StrictMono (target P) := by
  intro i j hij
  have he : i.val<j.val := hij
  have hm:=P.m_pos
  change (target P i).val<(target P j).val
  simp only [target]
  split_ifs <;> omega

theorem sourceA_class (P : Parameters) (i : Fin (2*P.p-1)) :
    (coordinateClass P (sourceA P i)).val=0 := by
  have hi:=i.isLt
  by_cases h : i.val<P.p
  · apply early_source_A
    simpa only [sourceA,h,if_true] using h
  · apply middle_source_A
    · simp only [sourceA,h,if_false]; omega
    · simp only [sourceA,h,if_false]; omega

theorem sourceB_class (P : Parameters) (i : Fin (2*P.q-1)) :
    (coordinateClass P (sourceB P i)).val=1 := by
  have hi:=i.isLt
  have he:=P.pq_eq
  by_cases h : i.val<P.q
  · apply early_source_B
    · simp only [sourceB,h,if_true]; omega
    · simp only [sourceB,h,if_true]; omega
  · apply middle_source_B
    · simp only [sourceB,h,if_false]; omega
    · simp only [sourceB,h,if_false]; omega

theorem target_class (P : Parameters) (i : Slot P.m) :
    (coordinateClass P (target P i)).val=
      if i.val<P.m then i.val+2 else 2*P.m-1-i.val+2 := by
  have hi:=i.isLt
  have hm:=P.m_pos
  by_cases h : i.val<P.m
  · have he:=early_target P (target P i)
      (by simp only [target,h,if_true]; omega)
      (by simp only [target,h,if_true]; omega)
    rw [he]
    simp only [target,h,if_true]
    omega
  · have he:=late_target P (target P i) (by simp only [target,h,if_false]; omega)
    rw [he]
    simp only [target,h,if_false]
    omega

theorem target_not_source (P : Parameters) (i : Slot P.m) : ¬sourceClass P (target P i) := by
  unfold sourceClass
  rw [target_class]
  split_ifs <;> omega

theorem sourceA_ne_B (P : Parameters) (i : Fin (2*P.p-1)) (j : Fin (2*P.q-1)) :
    sourceA P i ≠ sourceB P j := by
  intro h
  have he:=congrArg (fun k => (coordinateClass P k).val) h
  rw [sourceA_class,sourceB_class] at he
  omega

theorem sourceA_ne_target (P : Parameters) (i : Fin (2*P.p-1)) (j : Slot P.m) :
    sourceA P i ≠ target P j := by
  intro h
  apply target_not_source P j
  rw [← h]
  unfold sourceClass
  rw [sourceA_class]
  omega

theorem sourceB_ne_target (P : Parameters) (i : Fin (2*P.q-1)) (j : Slot P.m) :
    sourceB P i ≠ target P j := by
  intro h
  apply target_not_source P j
  rw [← h]
  unfold sourceClass
  rw [sourceB_class]
  omega

theorem coordinates_covered (P : Parameters) (i : Fin P.rank) :
    (∃ j,sourceA P j=i) ∨ (∃ j,sourceB P j=i) ∨ (∃ j,target P j=i) := by
  have hi:=i.isLt
  change i.val<4*P.m at hi
  have hp:=P.p_pos
  have hq:=P.q_pos
  have hm:=P.m_pos
  have he:=P.pq_eq
  by_cases h₁ : i.val<P.p
  · left
    refine ⟨⟨i.val,by omega⟩,?_⟩
    apply Fin.ext
    simp [sourceA,h₁]
  by_cases h₂ : i.val<P.m+1
  · right; left
    refine ⟨⟨i.val-P.p,by omega⟩,?_⟩
    apply Fin.ext
    simp only [sourceB]
    split_ifs <;> omega
  by_cases h₃ : i.val<2*P.m+1
  · right; right
    refine ⟨⟨i.val-(P.m+1),by omega⟩,?_⟩
    apply Fin.ext
    simp only [target]
    split_ifs <;> omega
  by_cases h₄ : i.val<2*P.m+P.p
  · left
    refine ⟨⟨i.val-(2*P.m+1)+P.p,by omega⟩,?_⟩
    apply Fin.ext
    simp only [sourceA]
    split_ifs <;> omega
  by_cases h₅ : i.val<3*P.m
  · right; left
    refine ⟨⟨i.val-(2*P.m+P.p)+P.q,by omega⟩,?_⟩
    apply Fin.ext
    simp only [sourceB]
    split_ifs <;> omega
  · right; right
    refine ⟨⟨i.val-2*P.m,by omega⟩,?_⟩
    apply Fin.ext
    simp only [target]
    split_ifs <;> omega

theorem target_pairing (P : Parameters) (i j : Slot P.m) :
    coordinateClass P (target P i)=coordinateClass P (target P j) ↔
      i=j ∨ i.val+j.val=2*P.m-1 := by
  have hi:=i.isLt
  have hj:=j.isLt
  have hm:=P.m_pos
  simp only [Fin.ext_iff,target_class]
  split_ifs <;> omega

theorem sourceA_precedes_target (P : Parameters) (i : Fin (2*P.p-1)) (j : Slot P.m) :
    sourceA P i<target P j ↔ j.rev.val≤(hallHeights P.m_pos P.p i.rev).val := by
  have hi:=i.isLt
  have hj:=j.isLt
  have hp:=P.p_pos
  have he:=P.pq_eq
  have hq:=P.q_pos
  change (sourceA P i).val<(target P j).val ↔ _
  simp only [sourceA,target,hallHeights,Fin.rev]
  split_ifs <;> omega

theorem sourceB_precedes_target (P : Parameters) (i : Fin (2*P.q-1)) (j : Slot P.m) :
    sourceB P i<target P j ↔ j.rev.val≤(hallHeights P.m_pos P.q i.rev).val := by
  have hi:=i.isLt
  have hj:=j.isLt
  have hp:=P.p_pos
  have he:=P.pq_eq
  have hq:=P.q_pos
  change (sourceB P i).val<(target P j).val ↔ _
  simp only [sourceB,target,hallHeights,Fin.rev]
  split_ifs <;> omega

end Schubert.RS.Family
