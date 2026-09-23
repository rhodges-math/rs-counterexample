import Schubert.RS.BoundedHeightMultiplicities
import Schubert.RS.SourceRows
import Schubert.RS.HallDeterminant

/-! Finite geometric products have exactly the complete homogeneous coefficients
in every degree up to the cutoff; negative coefficients vanish. -/

namespace Schubert.RS
noncomputable section
variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

def finiteSlotProduct (slot : ι → R) (B : ℕ) : AddMonoidAlgebra R ℤ :=
  ∏ h, ∑ a : Fin (B+1), AddMonoidAlgebra.single (a.val : ℤ) (slot h ^ a.val)

theorem finiteSlotProduct_expansion (slot : ι → R) (B : ℕ) :
    finiteSlotProduct slot B =
      ∑ e : ι → Fin (B+1), AddMonoidAlgebra.single (∑ h, ((e h).val : ℤ))
        (∏ h, slot h ^ (e h).val) := by
  classical
  rw [finiteSlotProduct, Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro e _
  exact AddMonoidAlgebra.prod_single _ _ _

theorem finiteSlotProduct_coefficient (slot : ι → R) (B : ℕ) (z : ℤ) :
    (finiteSlotProduct slot B).coeff z =
      ∑ e : ι → Fin (B+1), if (∑ h, ((e h).val : ℤ)) = z then
        (∏ h, slot h ^ (e h).val) else 0 := by
  rw [finiteSlotProduct_expansion]
  change laurentCoeffLinear z (∑ e : ι → Fin (B+1), _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp only [laurentCoeffLinear_apply, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem finiteSlotProduct_negative (slot : ι → R) (B : ℕ) {z : ℤ} (hz : z < 0) :
    (finiteSlotProduct slot B).coeff z = 0 := by
  classical
  rw [finiteSlotProduct_coefficient]
  apply Finset.sum_eq_zero
  intro e _
  have he : 0 ≤ ∑ h, ((e h).val : ℤ) := Finset.sum_nonneg (by intro h _; omega)
  exact if_neg (by omega)

theorem finiteSlotProduct_natural (slot : ι → R) (B k : ℕ) :
    (finiteSlotProduct slot B).coeff (k : ℤ) =
      ∑ e : {e : ι → Fin (B+1) // ∑ h, (e h).val = k}, ∏ h, slot h ^ (e.val h).val := by
  classical
  rw [finiteSlotProduct_coefficient]
  have hs := Finset.sum_subtype (p := fun e : ι → Fin (B+1) => ∑ h, (e h).val = k)
    (F := inferInstance) (Finset.univ.filter (fun e : ι → Fin (B+1) => ∑ h, (e h).val = k))
    (by intro e; simp) (fun e => ∏ h, slot h ^ (e h).val)
  rw [← hs, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  have he : (∑ h, ((e h).val : ℤ)) = (k : ℤ) ↔ ∑ h, (e h).val = k := by
    rw [← Nat.cast_sum, Int.natCast_inj]
  simp only [he]

theorem finiteSlotProduct_weak_heights {y : ℕ} (slot : Fin (y+1) → R)
    (B k : ℕ) (hk : k ≤ B) :
    (finiteSlotProduct slot B).coeff (k : ℤ) =
      ∑ r : HallLattice.WeakHeights k y, ∏ q, slot (r.val q) := by
  rw [finiteSlotProduct_natural]
  exact HallLattice.boundedMultiplicity_sum k y B hk slot

theorem finiteSlotProduct_completeHomogeneous {M : ℕ} (slot : Fin (M+1) → R)
    (y : Fin (M+1)) (B : ℕ) (z : ℤ) (hz : z ≤ B) :
    (finiteSlotProduct (fun h : Fin (y.val+1) => slot ⟨h.val, by have hh := h.isLt; have hy := y.isLt; omega⟩) B).coeff z =
      completeHomogeneous slot y z := by
  classical
  by_cases hnonneg : 0 ≤ z
  · have hk : z.toNat ≤ B := by have h := Int.toNat_of_nonneg hnonneg; omega
    rw [completeHomogeneous, if_pos hnonneg]
    convert finiteSlotProduct_weak_heights
      (fun h : Fin (y.val+1) => slot ⟨h.val, by have hh := h.isLt; have hy := y.isLt; omega⟩) B z.toNat hk using 1
    rw [Int.toNat_of_nonneg hnonneg]
  · rw [finiteSlotProduct_negative _ _ (by omega), completeHomogeneous, if_neg hnonneg]

end
end Schubert.RS
