import RSCounterexample.FlagVarieties.Foundations.Schemes.AffineSheafCoordinateRefinement
import RSCounterexample.FlagVarieties.Foundations.Schemes.AffineCoordinateSheafPresentation

/-!
# The Grassmannian point of an affine locally free quotient

The input is the epimorphism from the labelled free sheaf and local
rank-d sheaf trivializations. Finite projectivity and rank of global
sections are proved, and the resulting associated quotient preserves the
original epimorphism.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory QuotientPair
universe u
variable (A : CommRingCat.{u}) {n : ℕ} {M : (Spec A).Modules}
  (q : coordinateFreeSheaf (Spec A) n ⟶ M) [Epi q] (d : ℕ)
  (hfree : ∀ p : Spec A, ∃ U : (Spec A).Opens, p ∈ U ∧
    Nonempty (M.over U ≅
      SheafOfModules.free (R := (Spec A).ringCatSheaf.over U) (CoordinateIndex.{u} d)))

/-- The coordinate kernel of the given sheaf quotient defines the point. -/
def affineLocallyFreeGrassmannian : Module.Grassmannian A (Fin n → A) d := by
  letI := locally_coordinate_trivial_isQuasicoherent M d hfree
  letI := (locally_coordinate_trivial_finite_projective M d hfree).1
  letI := (locally_coordinate_trivial_finite_projective M d hfree).2
  exact affineCoordinateGrassmannian A q d (locally_coordinate_trivial_rank M d hfree)

/-- The associated quotient is the original sheaf, without a supplied module presentation. -/
def affineLocallyFreeGrassmannianSheafIso :
    coordinateQuotientSheaf A (affineLocallyFreeGrassmannian A q d hfree) ≅ M := by
  letI := locally_coordinate_trivial_isQuasicoherent M d hfree
  letI := (locally_coordinate_trivial_finite_projective M d hfree).1
  letI := (locally_coordinate_trivial_finite_projective M d hfree).2
  exact affineCoordinateGrassmannianSheafIso A q d (locally_coordinate_trivial_rank M d hfree)

@[reassoc]
theorem affineLocallyFreeGrassmannianSheafIso_source :
    coordinateQuotientSheafMap A (affineLocallyFreeGrassmannian A q d hfree) ≫
      (affineLocallyFreeGrassmannianSheafIso A q d hfree).hom = q := by
  let := locally_coordinate_trivial_isQuasicoherent M d hfree
  let := (locally_coordinate_trivial_finite_projective M d hfree).1
  let := (locally_coordinate_trivial_finite_projective M d hfree).2
  exact affineCoordinateGrassmannianSheafIso_source A q d
    (locally_coordinate_trivial_rank M d hfree)

end FlagVarieties.Foundations.QuotientCharts
