import Schubert.RS.Family.LaurentCoordinates
import Schubert.RS.Family.RootGrouping

/-! Exact images of individual roots under the source/target lattice map. -/

namespace Schubert.RS.Family
noncomputable section

theorem splitWeight_singleA (P : Parameters) (i : Fin (2*P.p-1)) (z : ℤ) :
    splitWeight P (Pi.single (sourceA P i) z)=(Pi.single i z,(0,0)) := by
  apply Prod.ext
  · funext j
    simp only [splitWeight,Pi.single_apply,(sourceA_strictMono P).injective.eq_iff]
  · apply Prod.ext
    · funext j
      simp [splitWeight,Pi.single_apply,sourceA_ne_B,(sourceA_ne_B P i j).symm]
    · funext j
      simp [splitWeight,Pi.single_apply,sourceA_ne_target,(sourceA_ne_target P i j.rev).symm]

theorem splitWeight_singleB (P : Parameters) (i : Fin (2*P.q-1)) (z : ℤ) :
    splitWeight P (Pi.single (sourceB P i) z)=(0,(Pi.single i z,0)) := by
  apply Prod.ext
  · funext j
    simp [splitWeight,Pi.single_apply,sourceA_ne_B,(sourceA_ne_B P j i).symm]
  · apply Prod.ext
    · funext j
      simp only [splitWeight,Pi.single_apply,(sourceB_strictMono P).injective.eq_iff]
    · funext j
      simp [splitWeight,Pi.single_apply,sourceB_ne_target,(sourceB_ne_target P i j.rev).symm]

theorem splitWeight_singleTarget (P : Parameters) (i : Slot P.m) (z : ℤ) :
    splitWeight P (Pi.single (target P i) z)=(0,(0,-Pi.single i.rev z)) := by
  apply Prod.ext
  · funext j
    simp [splitWeight,Pi.single_apply,sourceA_ne_target,(sourceA_ne_target P j i).symm]
  · apply Prod.ext
    · funext j
      simp [splitWeight,Pi.single_apply,sourceB_ne_target,(sourceB_ne_target P j i).symm]
    · funext j
      simp only [splitWeight,Pi.single_apply,Pi.neg_apply,(target_strictMono P).injective.eq_iff,
        Fin.rev_eq_iff]

theorem splitWeight_sub (P : Parameters) (v w : Weight P.rank) :
    splitWeight P (v-w)=splitWeight P v-splitWeight P w := (splitWeightEquiv P).map_sub v w

theorem splitWeight_nsmul (P : Parameters) (k : ℕ) (w : Weight P.rank) :
    splitWeight P (k • w)=k • splitWeight P w := (splitWeightEquiv P).toAddMonoidHom.map_nsmul k w

theorem splitWeight_sourceA (P : Parameters) (i j : Fin (2*P.p-1)) :
    splitWeight P (positiveRoot (sourceA P i) (sourceA P j))=(positiveRoot i j,(0,0)) := by
  rw [positiveRoot,splitWeight_sub,splitWeight_singleA,splitWeight_singleA]
  simp only [Prod.mk_sub_mk,sub_self]
  rfl

theorem splitWeight_sourceB (P : Parameters) (i j : Fin (2*P.q-1)) :
    splitWeight P (positiveRoot (sourceB P i) (sourceB P j))=(0,(positiveRoot i j,0)) := by
  rw [positiveRoot,splitWeight_sub,splitWeight_singleB,splitWeight_singleB]
  simp only [Prod.mk_sub_mk,sub_self]
  rfl

theorem splitWeight_sourceA_target (P : Parameters) (i : Fin (2*P.p-1)) (j : Slot P.m) :
    splitWeight P (positiveRoot (sourceA P i) (target P j))=(Pi.single i 1,(0,Pi.single j.rev 1)) := by
  rw [positiveRoot,splitWeight_sub,splitWeight_singleA,splitWeight_singleTarget]
  simp only [Prod.mk_sub_mk,sub_zero,sub_self,zero_sub,neg_neg]

theorem splitWeight_sourceB_target (P : Parameters) (i : Fin (2*P.q-1)) (j : Slot P.m) :
    splitWeight P (positiveRoot (sourceB P i) (target P j))=(0,(Pi.single i 1,Pi.single j.rev 1)) := by
  rw [positiveRoot,splitWeight_sub,splitWeight_singleB,splitWeight_singleTarget]
  simp only [Prod.mk_sub_mk,sub_zero,sub_self,zero_sub,neg_neg]

theorem splitWeight_targetPair (P : Parameters) (i : Fin P.m) :
    splitWeight P (positiveRoot (targetEarly P i) (targetLate P i))=
      (0,(0,positiveRoot (slotLeft i) (slotRight i))) := by
  rw [positiveRoot,targetEarly,targetLate,splitWeight_sub,splitWeight_singleTarget,splitWeight_singleTarget]
  simp only [Prod.mk_sub_mk,sub_self,slotRight,Fin.rev_rev]
  congr 2
  simp only [positiveRoot]
  abel

end
end Schubert.RS.Family
