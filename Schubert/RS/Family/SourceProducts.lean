import Schubert.RS.Family.NestedFactors
import Schubert.RS.Family.SourceSlots

/-! Reassemble all five root classes as two complete source expressions.
The two source ranks may differ. -/

namespace Schubert.RS.Family
noncomputable section
open Representation

theorem single_zero_prod {R G ι : Type*} [CommRing R] [AddCommMonoid G]
    (s : Finset ι) (f : ι → R) :
    AddMonoidAlgebra.single (0 : G) (∏ i ∈ s,f i)=∏ i ∈ s,AddMonoidAlgebra.single 0 (f i) :=
  map_prod (AddMonoidAlgebra.singleZeroRingHom : R →+* AddMonoidAlgebra R G) f s

theorem single_zero_mul {R G : Type*} [CommRing R] [AddMonoid G] (f g : R) :
    AddMonoidAlgebra.single (0 : G) (f*g)=AddMonoidAlgebra.single 0 f*AddMonoidAlgebra.single 0 g :=
  map_mul (AddMonoidAlgebra.singleZeroRingHom : R →+* AddMonoidAlgebra R G) f g

theorem internalA_product (P : Parameters) (B : ℕ) :
    (∏ r : PositiveRoot (2*P.p-1),nestedLaurent P (finiteLaurentRootFactor P B (groupedRoot P (.inl r))))=
      AddMonoidAlgebra.mapRingHom (Weight (2*P.p-1)) (Int.castRingHom (SourceBLaurent P))
        (weylFactor (2*P.p-1)) := by
  simp_rw [nested_internalA]
  exact mapped_weylFactor.symm

theorem internalB_product (P : Parameters) (B : ℕ) :
    (∏ r : PositiveRoot (2*P.q-1),nestedLaurent P (finiteLaurentRootFactor P B
      (groupedRoot P (.inr (.inl r)))))=
      AddMonoidAlgebra.single (0 : Weight (2*P.p-1))
        (AddMonoidAlgebra.mapRingHom (Weight (2*P.q-1)) (Int.castRingHom (SlotLaurent P.m))
          (weylFactor (2*P.q-1))) := by
  simp_rw [nested_internalB]
  rw [← single_zero_prod,mapped_weylFactor]

theorem target_pair_product (P : Parameters) (B : ℕ) :
    (∏ i : Fin P.m,nestedLaurent P (finiteLaurentRootFactor P B
      (groupedRoot P (.inr (.inr (.inl i))))))=
      AddMonoidAlgebra.single (0 : Weight (2*P.p-1))
        (AddMonoidAlgebra.single (0 : Weight (2*P.q-1)) (targetNumerator P.m)) := by
  simp_rw [nested_targetPair]
  rw [← single_zero_prod,← single_zero_prod]
  rfl

theorem crossA_product (P : Parameters) (B : ℕ) :
    (∏ s : SourceTargetA P,nestedLaurent P (finiteLaurentRootFactor P B
      (groupedRoot P (.inr (.inr (.inr (.inl s)))))))=
      ∏ i,sourceRow i (flagSourceRow (hallHeights P.m_pos P.p)
        (fun j => AddMonoidAlgebra.single 0 (slotVariable j) : Slot P.m → SourceBLaurent P) B i) := by
  simp_rw [nested_crossA]
  have hp (j : Slot P.m) (k : ℕ) : AddMonoidAlgebra.single (0 : Weight (2*P.q-1)) (slotVariable j^k)=
      (AddMonoidAlgebra.single 0 (slotVariable j) : SourceBLaurent P)^k := by
    rw [AddMonoidAlgebra.single_pow,smul_zero]
  simp_rw [hp]
  rw [source_target_slot_product (hallHeights P.m_pos P.p) (sourceA P) (target P)
    (sourceA_precedes_target P)
    (fun i j => ∑ k : Fin (B+1),AddMonoidAlgebra.single (Pi.single i (k.val : ℤ))
      ((AddMonoidAlgebra.single 0 (slotVariable j) : SourceBLaurent P)^k.val))]
  apply Finset.prod_congr rfl
  intro i _
  rw [flagSourceRow_factors]
  rfl

theorem crossB_product (P : Parameters) (B : ℕ) :
    (∏ s : SourceTargetB P,nestedLaurent P (finiteLaurentRootFactor P B
      (groupedRoot P (.inr (.inr (.inr (.inr s)))))))=
      AddMonoidAlgebra.single (0 : Weight (2*P.p-1))
        (∏ i,sourceRow i (flagSourceRow (hallHeights P.m_pos P.q) slotVariable B i)) := by
  simp_rw [nested_crossB]
  rw [← single_zero_prod,source_target_slot_product (hallHeights P.m_pos P.q) (sourceB P) (target P)
    (sourceB_precedes_target P)
    (fun i j => ∑ k : Fin (B+1),AddMonoidAlgebra.single (Pi.single i (k.val : ℤ)) (slotVariable j^k.val))]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [flagSourceRow_factors]
  rfl

theorem nested_finite_root_product (P : Parameters) (B : ℕ) :
    nestedLaurent P (rootCoordinateEmbedding (∏ r : PositiveRoot P.rank,finiteRootFactor P B r))=
      doubleSourceExpression (hallHeights P.m_pos P.p) (hallHeights P.m_pos P.q)
        slotVariable (targetNumerator P.m) B := by
  rw [finite_root_product_grouped,map_prod]
  simp only [GroupedRoot,Fintype.prod_sum_type]
  rw [internalA_product,internalB_product,target_pair_product,crossA_product,crossB_product]
  unfold doubleSourceExpression sourceExpression
  simp only [single_zero_mul]
  ring

end
end Schubert.RS.Family
