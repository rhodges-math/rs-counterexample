import Schubert.FlagVarieties.Foundations.Flags.ProjectiveGrassmannian
import Schubert.FlagVarieties.Foundations.Schemes.SelectedAffineClassification

/-!
Field-valued points of the selected quotient Grassmannian of quotient
rank `r` in dimension `r+1` are projective lines. The equivalence works over
every specified coefficient algebra `R → K`. This is a statement about
field-valued points only.
-/

noncomputable section
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u
variable (R K : Type u) [CommRing R] [Field K] [Algebra R K] (r : ℕ)

/-- Projective lines classify scheme morphisms over the given base. -/
def selectedProjectiveFieldEquiv :
    Projectivization K (Fin (r+1) → K) ≃
      {f : Spec (CommRingCat.of K) ⟶ selectedChartScheme R (r+1) r //
        f ≫ selectedChartSchemeToSpec R (r+1) r =
          Spec.map (CommRingCat.ofHom (algebraMap R K))} :=
  projectiveGrassmannianEquiv.trans selectedAffineQuotientEquiv

/-- The point associated to a projective line is the existing quotient map. -/
theorem selectedProjectiveFieldEquiv_val
    (p : Projectivization K (Fin (r+1) → K)) :
    (selectedProjectiveFieldEquiv R K r p).val =
      selectedQuotientMorphism R (projectiveGrassmannian p) := rfl

/-- Recovering the quotient of this morphism recovers exactly its line. -/
@[simp] theorem selectedProjectiveFieldEquiv_recovers_line
    (p : Projectivization K (Fin (r+1) → K)) :
    (quotientOfSelectedMorphism (selectedProjectiveFieldEquiv R K r p).val
      (selectedProjectiveFieldEquiv R K r p).property).toSubmodule = p.submodule := by
  change (quotientOfSelectedMorphism (selectedQuotientMorphism R _)
    (selectedQuotientMorphism_toSpec (P := projectiveGrassmannian p))).toSubmodule = _
  rw [quotientOfSelectedMorphism_selectedQuotientMorphism]
  rfl

/-- Every original quotient-scheme point comes from one unique projective line. -/
theorem selectedProjectiveField_existsUnique
    (f : Spec (CommRingCat.of K) ⟶ selectedChartScheme R (r+1) r)
    (hf : f ≫ selectedChartSchemeToSpec R (r+1) r =
      Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃! p : Projectivization K (Fin (r+1) → K),
      (selectedProjectiveFieldEquiv R K r p).val = f := by
  let e := selectedProjectiveFieldEquiv R K r
  refine ⟨e.symm ⟨f, hf⟩, ?_, ?_⟩
  · exact congrArg Subtype.val (e.apply_symm_apply ⟨f, hf⟩)
  · intro p hp
    apply e.injective
    exact (Subtype.ext hp).trans (e.apply_symm_apply ⟨f, hf⟩).symm

end FlagVarieties.Foundations.QuotientCharts
