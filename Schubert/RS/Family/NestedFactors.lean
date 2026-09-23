import Schubert.RS.Family.NestedCoordinates
import Schubert.RS.Family.FiniteFactors
import Schubert.RS.SourceExpressionFactors

namespace Schubert.RS.Family
noncomputable section
open Representation

theorem sourceA_isSource (P : Parameters) (i : Fin (2*P.p-1)) : sourceClass P (sourceA P i) := by
  change (coordinateClass P (sourceA P i)).val<2
  rw [sourceA_class]; omega

theorem sourceB_isSource (P : Parameters) (i : Fin (2*P.q-1)) : sourceClass P (sourceB P i) := by
  change (coordinateClass P (sourceB P i)).val<2
  rw [sourceB_class]; omega

theorem sourceA_target_different (P : Parameters) (i : Fin (2*P.p-1)) (j : Slot P.m) :
    coordinateClass P (sourceA P i) ≠ coordinateClass P (target P j) := by
  intro h
  apply target_not_source P j
  unfold sourceClass
  rw [← h,sourceA_class]; omega

theorem sourceB_target_different (P : Parameters) (i : Fin (2*P.q-1)) (j : Slot P.m) :
    coordinateClass P (sourceB P i) ≠ coordinateClass P (target P j) := by
  intro h
  apply target_not_source P j
  unfold sourceClass
  rw [← h,sourceB_class]; omega

theorem targetPair_same_class (P : Parameters) (i : Fin P.m) :
    coordinateClass P (targetEarly P i)=coordinateClass P (targetLate P i) :=
  (groupedRoot_relevant P (.inr (.inr (.inl i)))).resolve_right
    (fun h => target_not_source P (slotLeft i) h.1)

theorem single_zero_sum {R G ι : Type*} [CommRing R] [AddMonoid G]
    (s : Finset ι) (f : ι → R) :
    AddMonoidAlgebra.single (0 : G) (∑ i ∈ s,f i)=∑ i ∈ s,AddMonoidAlgebra.single 0 (f i) :=
  map_sum (AddMonoidAlgebra.singleZeroRingHom : R →+* AddMonoidAlgebra R G) f s

theorem nsmul_single_one {n : ℕ} (j : Fin n) (k : ℕ) :
    k • (Pi.single j 1 : Weight n)=Pi.single j (k : ℤ) := by
  rw [← Pi.single_smul]
  simp

theorem slotVariable_pow {m : ℕ} (j : Slot m) (k : ℕ) :
    slotVariable j^k=AddMonoidAlgebra.single (Pi.single j (k : ℤ)) 1 := by
  rw [slotVariable,AddMonoidAlgebra.single_pow,nsmul_single_one,one_pow]

theorem nested_internalA (P : Parameters) (B : ℕ) (r : PositiveRoot (2*P.p-1)) :
    nestedLaurent P (finiteLaurentRootFactor P B (groupedRoot P (.inl r)))=
      1-AddMonoidAlgebra.single (positiveRoot r.val.1 r.val.2) (1 : SourceBLaurent P) := by
  change nestedLaurent P (if coordinateClass P (sourceA P r.val.1)=coordinateClass P (sourceA P r.val.2)
    then _ else _)=_
  simp only [Fin.ext_iff,sourceA_class,if_true,map_sub,map_one,nestedLaurent_single,groupedRoot,splitWeight_sourceA]
  rfl

theorem nested_internalB (P : Parameters) (B : ℕ) (r : PositiveRoot (2*P.q-1)) :
    nestedLaurent P (finiteLaurentRootFactor P B (groupedRoot P (.inr (.inl r))))=
      AddMonoidAlgebra.single 0
        (1-AddMonoidAlgebra.single (positiveRoot r.val.1 r.val.2) (1 : SlotLaurent P.m)) := by
  change nestedLaurent P (if coordinateClass P (sourceB P r.val.1)=coordinateClass P (sourceB P r.val.2)
    then _ else _)=_
  simp only [Fin.ext_iff,sourceB_class,if_true,map_sub,map_one,nestedLaurent_single,groupedRoot,splitWeight_sourceB]
  rw [AddMonoidAlgebra.single_sub]
  rfl

theorem nested_targetPair (P : Parameters) (B : ℕ) (i : Fin P.m) :
    nestedLaurent P (finiteLaurentRootFactor P B (groupedRoot P (.inr (.inr (.inl i)))))=
      AddMonoidAlgebra.single 0 (AddMonoidAlgebra.single 0
        (1-AddMonoidAlgebra.single (positiveRoot (slotLeft i) (slotRight i)) (1 : ℤ))) := by
  change nestedLaurent P (if coordinateClass P (targetEarly P i)=coordinateClass P (targetLate P i)
    then _ else _)=_
  simp only [targetPair_same_class,if_true,map_sub,map_one,nestedLaurent_single,groupedRoot,splitWeight_targetPair]
  rw [AddMonoidAlgebra.single_sub,AddMonoidAlgebra.single_sub]
  rfl

theorem nested_crossA (P : Parameters) (B : ℕ) (s : SourceTargetA P) :
    nestedLaurent P (finiteLaurentRootFactor P B (groupedRoot P (.inr (.inr (.inr (.inl s))))))=
      ∑ k : Fin (B+1),AddMonoidAlgebra.single (Pi.single s.val.1 (k.val : ℤ))
        (AddMonoidAlgebra.single 0 (slotVariable s.val.2.rev^k.val)) := by
  change nestedLaurent P (if coordinateClass P (sourceA P s.val.1)=coordinateClass P (target P s.val.2)
    then _ else if sourceClass P (sourceA P s.val.1) ∧ ¬sourceClass P (target P s.val.2) then _ else _)=_
  simp only [sourceA_target_different,if_false,sourceA_isSource,target_not_source,
    not_false_eq_true,true_and,if_true,map_sum,groupedRoot]
  apply Finset.sum_congr rfl
  intro k _
  rw [nestedLaurent_single,splitWeight_nsmul,splitWeight_sourceA_target,slotVariable_pow]
  simp only [Prod.smul_mk,nsmul_single_one,smul_zero]

theorem nested_crossB (P : Parameters) (B : ℕ) (s : SourceTargetB P) :
    nestedLaurent P (finiteLaurentRootFactor P B (groupedRoot P (.inr (.inr (.inr (.inr s))))))=
      AddMonoidAlgebra.single 0
        (∑ k : Fin (B+1),AddMonoidAlgebra.single (Pi.single s.val.1 (k.val : ℤ))
          (slotVariable s.val.2.rev^k.val)) := by
  change nestedLaurent P (if coordinateClass P (sourceB P s.val.1)=coordinateClass P (target P s.val.2)
    then _ else if sourceClass P (sourceB P s.val.1) ∧ ¬sourceClass P (target P s.val.2) then _ else _)=_
  simp only [sourceB_target_different,if_false,sourceB_isSource,target_not_source,
    not_false_eq_true,true_and,if_true,map_sum,groupedRoot]
  rw [single_zero_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [nestedLaurent_single,splitWeight_nsmul,splitWeight_sourceB_target,slotVariable_pow]
  simp only [Prod.smul_mk,nsmul_single_one,smul_zero]

end
end Schubert.RS.Family
