import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedMorphismQuotient

/-!
# Affine-morphism classification by coordinate quotients

For every coefficient algebra, incoming morphisms to the glued chart
scheme over the base correspond to finite-projective
coordinate quotients. Both inverse identities are proved. The universal
quotient sheaf is constructed in `Schemes/SelectedUniversalQuotient.lean`, and
families over arbitrary schemes are classified in
`Schemes/GlobalLocallyFreeQuotient.lean`.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {n d : ℕ}

/-- Recover the finite-projective quotient from any incoming affine map over the base. -/
def quotientOfSelectedMorphism
    (F : Spec (CommRingCat.of A) ⟶ selectedChartScheme R n d)
    (hF : F ≫ selectedChartSchemeToSpec R n d =
      Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    Module.Grassmannian A (Fin n → A) d :=
  (selectedMorphismFiniteCover F hF).quotient

/-- The recovered quotient gives exactly the original scheme morphism. -/
theorem selectedQuotientMorphism_quotientOfSelectedMorphism
    (F : Spec (CommRingCat.of A) ⟶ selectedChartScheme R n d)
    (hF : F ≫ selectedChartSchemeToSpec R n d =
      Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    selectedQuotientMorphism R (quotientOfSelectedMorphism F hF) = F :=
  (selectedMorphismFiniteCover F hF).quotient_morphism

/-- Applying the recovery construction to a quotient's map returns that quotient. -/
theorem quotientOfSelectedMorphism_selectedQuotientMorphism
    (P : Module.Grassmannian A (Fin n → A) d) :
    quotientOfSelectedMorphism (selectedQuotientMorphism R P)
      (selectedQuotientMorphism_toSpec (P := P)) = P := by
  apply selectedQuotientMorphism_injective (R := R)
  exact selectedQuotientMorphism_quotientOfSelectedMorphism _ _

/-- The glued chart scheme classifies all finite-projective coordinate quotients on affine bases. -/
def selectedAffineQuotientEquiv :
    Module.Grassmannian A (Fin n → A) d ≃
      { F : Spec (CommRingCat.of A) ⟶ selectedChartScheme R n d //
        F ≫ selectedChartSchemeToSpec R n d =
          Spec.map (CommRingCat.ofHom (algebraMap R A)) } where
  toFun P := ⟨selectedQuotientMorphism R P, selectedQuotientMorphism_toSpec⟩
  invFun F := quotientOfSelectedMorphism F.val F.property
  left_inv := quotientOfSelectedMorphism_selectedQuotientMorphism
  right_inv F := Subtype.ext (selectedQuotientMorphism_quotientOfSelectedMorphism F.val F.property)

/-- Every incoming affine map over the base has exactly one quotient preimage. -/
theorem selectedQuotientMorphism_existsUnique
    (F : Spec (CommRingCat.of A) ⟶ selectedChartScheme R n d)
    (hF : F ≫ selectedChartSchemeToSpec R n d =
      Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    ∃! P : Module.Grassmannian A (Fin n → A) d, selectedQuotientMorphism R P = F := by
  refine ⟨quotientOfSelectedMorphism F hF,
    selectedQuotientMorphism_quotientOfSelectedMorphism F hF, ?_⟩
  intro P hP
  apply selectedQuotientMorphism_injective (R := R)
  rw [hP, selectedQuotientMorphism_quotientOfSelectedMorphism]

end FlagVarieties.Foundations.QuotientCharts
