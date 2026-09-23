import Schubert.RS.SourceAlternant
import Schubert.RS.SourceRows

/-! The determinant equality in the source-extraction lemma.
The rows are finite Laurent polynomials over an arbitrary coefficient ring. -/

namespace Schubert.RS

noncomputable section
variable {R : Type*} [CommRing R]

set_option backward.isDefEq.respectTransparency false in
theorem source_weyl_determinant (d : ℕ) :
    AddMonoidAlgebra.mapRingHom (Weight d) (Int.castRingHom R) (weylFactor d) =
      Matrix.det (fun i j : Fin d =>
        sourceRow i (AddMonoidAlgebra.single ((j.val : ℤ) - i.val) (1 : R))) := by
  rw [weylFactor_eq_determinant, RingHom.map_det]
  congr 1
  funext i j
  simp [Matrix.map_apply, coordinatePower, sourceRow_single]

set_option backward.isDefEq.respectTransparency false in
/-- Extract all source exponents at once. The matrix entry is the coefficient
in degree `1 + i - j`, exactly as in the manuscript. -/
theorem source_extraction_determinant (d : ℕ)
    (p : Fin d → AddMonoidAlgebra R ℤ) :
    (AddMonoidAlgebra.mapRingHom (Weight d) (Int.castRingHom R) (weylFactor d) *
        ∏ i, sourceRow i (p i)).coeff (fun _ => 1) =
      Matrix.det (fun i j : Fin d => (p i).coeff (1 + i.val - j.val)) := by
  rw [source_weyl_determinant]
  exact coefficient_source_alternant d p (fun _ => 1)

end
end Schubert.RS
