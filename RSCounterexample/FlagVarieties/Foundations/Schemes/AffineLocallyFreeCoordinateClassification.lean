import RSCounterexample.FlagVarieties.Foundations.Schemes.AffineLocallyFreeCoordinateQuotient
import RSCounterexample.FlagVarieties.Foundations.Schemes.AffineCoordinateSheafUniqueness

/-!
# Unique coordinate presentation of an affine locally free quotient sheaf

Existence and uniqueness use the original source map. Arbitrary changes
of the quotient target are allowed exactly when that map is preserved.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u
variable (A : CommRingCat.{u}) {n : ℕ} {M : (Spec A).Modules}
  (q : coordinateFreeSheaf (Spec A) n ⟶ M) [Epi q] (d : ℕ)
  (hfree : ∀ p : Spec A, ∃ U : (Spec A).Opens, p ∈ U ∧
    Nonempty (M.over U ≅
      SheafOfModules.free (R := (Spec A).ringCatSheaf.over U) (CoordinateIndex.{u} d)))

include hfree

theorem affineLocallyFreeGrassmannian_unique
    (P : Module.Grassmannian A (Fin n → A) d)
    (e : coordinateQuotientSheaf A P ≅ M)
    (he : coordinateQuotientSheafMap A P ≫ e.hom = q) :
    P = affineLocallyFreeGrassmannian A q d hfree := by
  apply coordinateQuotient_eq_of_sheaf_iso A P _
    (e ≪≫ (affineLocallyFreeGrassmannianSheafIso A q d hfree).symm)
  simp only [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, he]
  apply (cancel_mono (affineLocallyFreeGrassmannianSheafIso A q d hfree).hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    (affineLocallyFreeGrassmannianSheafIso_source A q d hfree).symm

/-- Every affine locally free quotient has exactly one coordinate-kernel presentation. -/
theorem affineLocallyFreeGrassmannian_existsUnique :
    ∃! P : Module.Grassmannian A (Fin n → A) d,
      ∃ e : coordinateQuotientSheaf A P ≅ M,
        coordinateQuotientSheafMap A P ≫ e.hom = q := by
  refine ⟨affineLocallyFreeGrassmannian A q d hfree,
    ⟨affineLocallyFreeGrassmannianSheafIso A q d hfree,
      affineLocallyFreeGrassmannianSheafIso_source A q d hfree⟩, ?_⟩
  rintro P ⟨e, he⟩
  exact affineLocallyFreeGrassmannian_unique A q d hfree P e he

end FlagVarieties.Foundations.QuotientCharts
