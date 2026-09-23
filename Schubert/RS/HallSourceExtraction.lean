import Schubert.RS.FiniteSlotProduct
import Schubert.RS.SourceExtractionDet

/-! Complete source extraction: finite geometric factors, the whole source
Weyl factor, and the Hall polynomial are connected by proved equalities. -/

namespace Schubert.RS
noncomputable section
variable {R : Type*} [CommRing R] {d M : ℕ}

def flagSourceRow (y : Fin d → Fin (M+1)) (slot : Fin (M+1) → R) (B : ℕ)
    (i : Fin d) : AddMonoidAlgebra R ℤ :=
  finiteSlotProduct (fun h : Fin ((y i.rev).val+1) =>
    slot ⟨h.val, by have hh := h.isLt; have hy := (y i.rev).isLt; omega⟩) B

theorem flagSourceRow_coefficient (y : Fin d → Fin (M+1)) (slot : Fin (M+1) → R)
    (B : ℕ) (hB : d ≤ B) (i j : Fin d) :
    (flagSourceRow y slot B i).coeff (1+(i.val : ℤ)-j.val) =
      completeHomogeneous slot (y i.rev) (1+(i.val : ℤ)-j.val) := by
  apply finiteSlotProduct_completeHomogeneous
  have hi := i.isLt
  omega

/-- The source extraction lemma in reversed-slot conventions. Every finite
geometric term and every source Weyl term is retained before extraction. -/
theorem hall_source_extraction (y : Fin d → Fin (M+1))
    (hy : Monotone (fun i => (y i).val)) (slot : Fin (M+1) → R)
    (B : ℕ) (hB : d ≤ B) :
    (AddMonoidAlgebra.mapRingHom (Weight d) (Int.castRingHom R) (weylFactor d) *
      ∏ i, sourceRow i (flagSourceRow y slot B i)).coeff (fun _ => 1) =
      ∑ r : HallLattice.StrictHeights y, ∏ i, slot ⟨(r.val i).val, by
        have h := (y i).isLt; have hr := (r.val i).isLt; omega⟩ := by
  classical
  rw [source_extraction_determinant]
  simp_rw [flagSourceRow_coefficient y slot B hB]
  let A : Matrix (Fin d) (Fin d) R := fun i j =>
    completeHomogeneous slot (y i.rev) (1+(i.val : ℤ)-j.val)
  change Matrix.det A = _
  rw [← Matrix.det_submatrix_equiv_self Fin.revPerm A]
  have hm : A.submatrix Fin.revPerm Fin.revPerm =
      (fun i j : Fin d => completeHomogeneous slot (y i) (1-(i.val : ℤ)+j.val)) := by
    funext i j
    change completeHomogeneous slot (y i.rev.rev) (1+(i.rev.val : ℤ)-j.rev.val) = _
    rw [Fin.rev_rev]
    congr 1
    have hi := i.isLt
    have hj := j.isLt
    simp only [Fin.val_rev]
    omega
  rw [hm]
  exact HallLattice.hall_determinant y slot hy

end
end Schubert.RS
