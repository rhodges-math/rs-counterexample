import Schubert.RS.HallSourceExtraction

/-! Extract two independent source classes, retaining the target numerator. -/

namespace Schubert.RS
noncomputable section
variable {R : Type*} [CommRing R] {d M : ℕ}

def hallPolynomial (y : Fin d → Fin (M+1)) (slot : Fin (M+1) → R) : R :=
  ∑ r : HallLattice.StrictHeights y, ∏ i,
    slot ⟨(r.val i).val, by have h := (y i).isLt; have hr := (r.val i).isLt; omega⟩

theorem hallPolynomial_map {S : Type*} [CommRing S] (f : R →+* S)
    (y : Fin d → Fin (M+1)) (slot : Fin (M+1) → R) :
    hallPolynomial y (fun j => f (slot j)) = f (hallPolynomial y slot) := by
  simp only [hallPolynomial, map_sum, map_prod]

def sourceExpression (y : Fin d → Fin (M+1)) (slot : Fin (M+1) → R) (B : ℕ) :
    AddMonoidAlgebra R (Weight d) :=
  AddMonoidAlgebra.mapRingHom (Weight d) (Int.castRingHom R) (weylFactor d) *
    ∏ i, sourceRow i (flagSourceRow y slot B i)

theorem sourceExpression_coefficient (y : Fin d → Fin (M+1))
    (hy : Monotone (fun i => (y i).val)) (slot : Fin (M+1) → R) (B : ℕ) (hB : d ≤ B) :
    (sourceExpression y slot B).coeff (fun _ => 1) = hallPolynomial y slot :=
  hall_source_extraction y hy slot B hB

def doubleSourceExpression {e : ℕ} (y : Fin d → Fin (M+1)) (z : Fin e → Fin (M+1))
    (slot : Fin (M+1) → R) (Q : R) (B : ℕ) :
    AddMonoidAlgebra (AddMonoidAlgebra R (Weight e)) (Weight d) :=
  AddMonoidAlgebra.single 0 (sourceExpression z slot B * AddMonoidAlgebra.single 0 Q) *
    sourceExpression y (fun j => AddMonoidAlgebra.single 0 (slot j) : Fin (M+1) →
      AddMonoidAlgebra R (Weight e)) B

theorem double_source_extraction {e : ℕ}
    (y : Fin d → Fin (M+1)) (hy : Monotone (fun i => (y i).val))
    (z : Fin e → Fin (M+1)) (hz : Monotone (fun i => (z i).val))
    (slot : Fin (M+1) → R) (Q : R) (B : ℕ) (hB : d ≤ B) (hB' : e ≤ B) :
    ((doubleSourceExpression y z slot Q B).coeff (fun _ => 1)).coeff (fun _ => 1) =
      Q * hallPolynomial y slot * hallPolynomial z slot := by
  unfold doubleSourceExpression
  rw [AddMonoidAlgebra.coeff_single_mul_apply, neg_zero, zero_add,
    sourceExpression_coefficient y hy _ B hB]
  have he : hallPolynomial y
      (fun j => AddMonoidAlgebra.single 0 (slot j) : Fin (M+1) → AddMonoidAlgebra R (Weight e)) =
      AddMonoidAlgebra.single 0 (hallPolynomial y slot) :=
    hallPolynomial_map (AddMonoidAlgebra.singleZeroRingHom : R →+* AddMonoidAlgebra R (Weight e)) y slot
  rw [he, mul_assoc, AddMonoidAlgebra.single_mul_single, zero_add,
    AddMonoidAlgebra.coeff_mul_single_apply, neg_zero, add_zero,
    sourceExpression_coefficient z hz slot B hB']
  ring

end
end Schubert.RS
