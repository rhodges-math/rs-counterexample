import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedQuotientCoverBaseChange

/-!
# Naturality of the quotient-to-scheme construction

The complete scheme morphism, including its structure-sheaf map, commutes
with arbitrary scalar extension. The proof compares the extended
principal presentations and then uses the proved independence of covers.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory

universe u

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] {n d : ℕ}

/-- The intrinsic quotient morphism commutes with the existing scalar tower. -/
@[reassoc] theorem selectedQuotientMorphism_baseChange [Algebra A B] [IsScalarTower R A B]
    (P : Module.Grassmannian A (Fin n → A) d) :
    Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ selectedQuotientMorphism R P =
      selectedQuotientMorphism R (coordinateGrassmannianBaseChange B P) := by
  let D := selectedQuotientCover R A P
  apply (D.baseChange B).schemeCover.hom_ext
  intro i
  rw [← Category.assoc, ← D.localBaseChange_square B i, Category.assoc,
    D.ι_selectedQuotientMorphism, (D.baseChange B).ι_selectedQuotientMorphism,
    D.baseChange_chartMap]

/-- Naturality holds for every algebra homomorphism, without flatness or injectivity. -/
theorem selectedQuotientMorphism_naturality (g : A →ₐ[R] B)
    (P : Module.Grassmannian A (Fin n → A) d) :
    letI : Algebra A B := g.toAlgebra
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ selectedQuotientMorphism R P =
      selectedQuotientMorphism R (coordinateGrassmannianBaseChange B P) := by
  let : Algebra A B := g.toAlgebra
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  exact selectedQuotientMorphism_baseChange P

end FlagVarieties.Foundations.QuotientCharts
