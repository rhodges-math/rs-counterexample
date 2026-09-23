import Schubert.RS.JosephPolo.ColumnProducts

namespace Schubert.RS.Representation
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Every finite column shape has an ordered realization, including the
empty shape and rank zero. The order is irrelevant to its multiplicities. -/
theorem exists_columnMultiplicity {n : ℕ} (m : ColumnShape n) :
    ∃ (d : ℕ) (h : Fin d → Fin n), columnMultiplicity h = m := by
  let I := Σ k : Fin n, Fin (m k)
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let h : Fin (Fintype.card I) → Fin n := fun j => (e.symm j).1
  refine ⟨Fintype.card I,h,?_⟩
  funext k
  let f : {j : Fin (Fintype.card I) // h j=k} ≃ {x : I // x.1=k} :=
    Equiv.subtypeEquiv e.symm (fun _ => Iff.rfl)
  let g : {x : I // x.1=k} ≃ Fin (m k) := {
    toFun := fun x => x.property ▸ x.val.2
    invFun := fun j => ⟨⟨k,j⟩,rfl⟩
    left_inv := by rintro ⟨⟨a,j⟩,ha⟩; cases ha; rfl
    right_inv := fun _ => rfl }
  exact (Fintype.card_congr (f.trans g)).trans (Fintype.card_fin (m k))

end
end Schubert.RS.Representation
