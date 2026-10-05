import Schubert.FlagVarieties.Foundations.Schemes.SelectedChartOverlapClosed
import Schubert.FlagVarieties.Foundations.Schemes.SelectedUniversalOverlap
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Separatedness of the quotient Grassmannian

On every pair of the original affine charts, the relative diagonal is the
closed immersion of the determinant intersection proved earlier.
The affine-cover criterion then proves separatedness of the glued scheme.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

variable (R : Type u) [CommRing R] {n d : ℕ} (a b : Fin d ↪ Fin n)

theorem selectedChartDiagonal_comparison :
    (selectedChartOverlap_isPullback R a b).isoPullback.hom ≫
      pullback.mapDesc (selectedChartSchemeChart R n d a) (selectedChartSchemeChart R n d b)
        (selectedChartSchemeToSpec R n d) ≫
      (pullback.congrHom (selectedChartSchemeChart_toSpec R n d a)
        (selectedChartSchemeChart_toSpec R n d b)).hom =
      selectedChartOverlapToProduct R a b := by
  apply pullback.hom_ext
  · simp [pullback.mapDesc]
  · simp [pullback.mapDesc]

instance selectedChartDiagonal_isClosedImmersion :
    IsClosedImmersion (pullback.mapDesc
      (selectedChartSchemeChart R n d a) (selectedChartSchemeChart R n d b)
      (selectedChartSchemeToSpec R n d)) := by
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion
    (selectedChartOverlap_isPullback R a b).isoPullback.hom]
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _
    (pullback.congrHom (selectedChartSchemeChart_toSpec R n d a)
      (selectedChartSchemeChart_toSpec R n d b)).hom]
  rw [Category.assoc, selectedChartDiagonal_comparison]
  infer_instance

/-- The original glued quotient scheme is separated over its coefficient ring. -/
instance selectedChartSchemeToSpec_isSeparated (n d : ℕ) :
    IsSeparated (selectedChartSchemeToSpec R n d) := by
  rw [IsSeparated.isSeparated_eq_diagonal_isClosedImmersion]
  rw [← HasAffineProperty.diagonal_iff @IsClosedImmersion]
  let := HasAffineProperty.isLocal_affineProperty @IsClosedImmersion
  let C := (selectedChartGlueData R n d).openCover
  have : ∀ i, IsAffine (C.X i) := fun _ => inferInstanceAs (IsAffine
    (Spec (CommRingCat.of (MvPolynomial (Fin d × Fin (n-d)) R))))
  refine AffineTargetMorphismProperty.diagonal_of_openCover_source
    (Q := fun {X _} f _ => IsAffine X ∧ Function.Surjective f.appTop)
    (selectedChartSchemeToSpec R n d) C ?_
  intro i j
  apply (HasAffineProperty.iff_of_isAffine (P := @IsClosedImmersion)).mp
  exact selectedChartDiagonal_isClosedImmersion R i.down j.down

instance selectedChartScheme_isSeparated (n d : ℕ) :
    (selectedChartScheme R n d).IsSeparated := by
  constructor
  rw [← terminal.comp_from (selectedChartSchemeToSpec R n d)]
  infer_instance

end FlagVarieties.Foundations.QuotientCharts
