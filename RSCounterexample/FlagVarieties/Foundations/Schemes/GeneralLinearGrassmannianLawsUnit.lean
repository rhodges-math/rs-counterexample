import RSCounterexample.FlagVarieties.Foundations.Schemes.GeneralLinearGrassmannianEvaluation

/-! Identity-matrix evaluation of the varying morphism. The group
scheme unit is the vendor's coordinate counit. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Matrix
universe u
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] (n d : ℕ)

/-- The identity `B`-point of `GLₙ`, through the counit of `𝒪(GLₙ)`. -/
def generalLinearUnitAlgebraPoint :
    TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] B :=
  (Algebra.ofId R B).comp (TauCeti.GeneralLinear.counit R n)

theorem generalLinearMatrixAt_unit :
    generalLinearMatrixAt R B n (generalLinearUnitAlgebraPoint R B n) = 1 := by
  calc
    generalLinearMatrixAt R B n (generalLinearUnitAlgebraPoint R B n) =
        ((TauCeti.GeneralLinear.localizedGenericMatrix R n).map
          (TauCeti.GeneralLinear.counit R n)).map (Algebra.ofId R B) := by
      ext i j
      rfl
    _ = (1 : Matrix (Fin n) (Fin n) R).map (Algebra.ofId R B) := by
      rw [TauCeti.GeneralLinear.map_counit_localizedGenericMatrix]
    _ = 1 := by simp

/-- Unit evaluation fixes every original affine Grassmannian point as an
equality of its classifying scheme morphism. -/
theorem generalLinearGrassmannianAction_unit_affine
    (P : Module.Grassmannian B (Fin n → B) d) :
    generalLinearGrassmannianOfAffine R B n d
        (generalLinearUnitAlgebraPoint R B n) P ≫
      generalLinearGrassmannianAction R n d = selectedQuotientMorphism R P := by
  rw [generalLinearGrassmannianAction_evaluate]
  have he : ((generalLinearMatrixAt R B n
      (generalLinearUnitAlgebraPoint R B n)).toLinearEquiv'
        (generalLinearMatrixAt_isUnit R B n
          (generalLinearUnitAlgebraPoint R B n)).invertible) =
      LinearEquiv.refl B (Fin n → B) := by
    apply LinearEquiv.ext
    intro x
    change generalLinearMatrixAt R B n
      (generalLinearUnitAlgebraPoint R B n) *ᵥ x = x
    rw [generalLinearMatrixAt_unit]
    simp
  rw [he, grassmannianTransport_refl]

end FlagVarieties.Foundations.QuotientCharts
