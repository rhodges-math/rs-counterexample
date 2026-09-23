import Schubert.RS.DoubleSourceExtraction
import Schubert.RS.WeylRootSeries

/-! Factor forms of the exact source expression, over any coefficient ring. -/

namespace Schubert.RS
noncomputable section
open Representation
variable {R : Type*} [CommRing R] {d M : ℕ}

def sourceWeightHom (i : Fin d) : ℤ →+ Weight d where
  toFun k := Pi.single i k
  map_zero' := by simp
  map_add' k l := by simp [Pi.single_add]

def sourceRowRing (i : Fin d) : AddMonoidAlgebra R ℤ →+* AddMonoidAlgebra R (Weight d) :=
  AddMonoidAlgebra.mapDomainRingHom R (sourceWeightHom i)

theorem sourceRowRing_apply (i : Fin d) (p : AddMonoidAlgebra R ℤ) :
    sourceRowRing i p = sourceRow i p := rfl

theorem sourceRowRing_single (i : Fin d) (k : ℤ) (r : R) :
    sourceRowRing i (AddMonoidAlgebra.single k r) = AddMonoidAlgebra.single (Pi.single i k) r :=
  AddMonoidAlgebra.mapDomain_single

theorem mapped_weylFactor :
    AddMonoidAlgebra.mapRingHom (Weight d) (Int.castRingHom R) (weylFactor d) =
      ∏ r : PositiveRoot d, (1-AddMonoidAlgebra.single (positiveRoot r.val.1 r.val.2) (1 : R)) := by
  unfold weylFactor
  simp only [map_prod, map_sub, map_one, AddMonoidAlgebra.mapRingHom_single, Int.cast_one]
  exact positiveRoot_product _

theorem flagSourceRow_factors (y : Fin d → Fin (M+1)) (slot : Fin (M+1) → R)
    (B : ℕ) (i : Fin d) :
    sourceRow i (flagSourceRow y slot B i) =
      ∏ h : Fin ((y i.rev).val+1), ∑ k : Fin (B+1),
        AddMonoidAlgebra.single (Pi.single i (k.val : ℤ))
          (slot ⟨h.val, by have hh := h.isLt; have hy := (y i.rev).isLt; omega⟩ ^ k.val) := by
  rw [← sourceRowRing_apply]
  unfold flagSourceRow finiteSlotProduct
  simp only [map_prod, map_sum, sourceRowRing_single]

theorem sourceExpression_factors (y : Fin d → Fin (M+1)) (slot : Fin (M+1) → R) (B : ℕ) :
    sourceExpression y slot B =
      (∏ r : PositiveRoot d, (1-AddMonoidAlgebra.single (positiveRoot r.val.1 r.val.2) (1 : R))) *
      ∏ i, ∏ h : Fin ((y i.rev).val+1), ∑ k : Fin (B+1),
        AddMonoidAlgebra.single (Pi.single i (k.val : ℤ))
          (slot ⟨h.val, by have hh := h.isLt; have hy := (y i.rev).isLt; omega⟩ ^ k.val) := by
  rw [sourceExpression, mapped_weylFactor]
  simp_rw [flagSourceRow_factors]

end
end Schubert.RS
