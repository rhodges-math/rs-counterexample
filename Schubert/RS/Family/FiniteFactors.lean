import Schubert.RS.Family.RootGrouping

namespace Schubert.RS.Family
noncomputable section
open Representation

def finiteLaurentRootFactor (P : Parameters) (B : ℕ) (r : PositiveRoot P.rank) : Laurent P.rank :=
  if coordinateClass P r.val.1=coordinateClass P r.val.2 then
    1-AddMonoidAlgebra.single (positiveRoot r.val.1 r.val.2) 1
  else if sourceClass P r.val.1 ∧ ¬sourceClass P r.val.2 then
    ∑ k : Fin (B+1),AddMonoidAlgebra.single (k.val • positiveRoot r.val.1 r.val.2) 1
  else 1

theorem rootCoordinateEmbedding_monomial {n : ℕ} (d : RootDegree n) (z : ℤ) :
    rootCoordinateEmbedding (MvPolynomial.monomial d z)=AddMonoidAlgebra.single (rootWeight d) z :=
  AddMonoidAlgebra.mapDomain_single

theorem finiteRootFactor_embedding (P : Parameters) (B : ℕ) (r : PositiveRoot P.rank) :
    rootCoordinateEmbedding (finiteRootFactor P B r)=finiteLaurentRootFactor P B r := by
  classical
  unfold finiteRootFactor finiteLaurentRootFactor
  split_ifs
  · rw [map_sub,map_one,rootCoordinateEmbedding_monomial,rootWeight_rootDegree _ _ r.property]
  · rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [rootCoordinateEmbedding_monomial,rootWeight_nsmul,rootWeight_rootDegree _ _ r.property]
  · exact map_one _

theorem finite_root_product_grouped (P : Parameters) (B : ℕ) :
    rootCoordinateEmbedding (∏ r : PositiveRoot P.rank,finiteRootFactor P B r)=
      ∏ s : GroupedRoot P,finiteLaurentRootFactor P B (groupedRoot P s) := by
  rw [map_prod]
  simp_rw [finiteRootFactor_embedding]
  apply product_groupedRoot
  intro r hr
  have hc : coordinateClass P r.val.1 ≠ coordinateClass P r.val.2 := fun h => hr (Or.inl h)
  have hs : ¬(sourceClass P r.val.1 ∧ ¬sourceClass P r.val.2) := fun h => hr (Or.inr h)
  simp only [finiteLaurentRootFactor,if_neg hc,if_neg hs]

end
end Schubert.RS.Family
