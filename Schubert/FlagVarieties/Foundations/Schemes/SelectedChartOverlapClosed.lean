import Schubert.FlagVarieties.Foundations.Schemes.SelectedChartOverlapDeterminant
import Schubert.FlagVarieties.Foundations.Schemes.SelectedChartSchemeStructure
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # The overlap is closed in the product of the two affine charts

The two coordinate maps jointly generate the determinant localization:
the first supplies polynomial numerators and the second supplies the inverse
denominator. This proves a closed immersion over the original coefficient ring.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R] {n d : ℕ} (a b : Fin d ↪ Fin n)

/-- Coordinate map from the relative product of the two original charts. -/
def selectedOverlapTensorCoordinates :
    (MvPolynomial (Fin d × Fin (n-d)) R ⊗[R] MvPolynomial (Fin d × Fin (n-d)) R) →ₐ[R]
      Localization.Away (selectedPolynomialBlock R a b).det :=
  Algebra.TensorProduct.lift
    (IsScalarTower.toAlgHom R (MvPolynomial (Fin d × Fin (n-d)) R)
      (Localization.Away (selectedPolynomialBlock R a b).det))
    (matrixOverlapCoordinates R (selectedPolynomialBlock R a b) (remainingPolynomialBlock R a b))
    (fun _ _ => Commute.all _ _)

theorem selectedOverlapTensorCoordinates_surjective :
    Function.Surjective (selectedOverlapTensorCoordinates R a b) := by
  intro z
  obtain ⟨k, p, hp⟩ := IsLocalization.Away.surj (selectedPolynomialBlock R a b).det z
  refine ⟨p ⊗ₜ[R] ((selectedPolynomialBlock R b a).det ^ k), ?_⟩
  simp only [selectedOverlapTensorCoordinates, Algebra.TensorProduct.lift_tmul, map_pow]
  change algebraMap _ (Localization.Away (selectedPolynomialBlock R a b).det) p *
    (matrixOverlapCoordinates R (selectedPolynomialBlock R a b) (remainingPolynomialBlock R a b)
      (selectedPolynomialBlock R b a).det) ^ k = z
  rw [← hp, mul_assoc, ← mul_pow, selectedOverlapCoordinates_det_mul, one_pow, mul_one]

/-- The determinant intersection maps to the relative product of its two charts. -/
def selectedChartOverlapToProduct :
    Spec (CommRingCat.of (Localization.Away (selectedPolynomialBlock R a b).det)) ⟶
      pullback (selectedChartToSpec R n d) (selectedChartToSpec R n d) :=
  pullback.lift (selectedChartOverlapInclusion R a b) (selectedChartOverlapMap R a b)
    (selectedChartOverlapMap_toSpec R a b).symm

@[reassoc (attr := simp)] theorem selectedChartOverlapToProduct_fst :
    selectedChartOverlapToProduct R a b ≫ pullback.fst _ _ =
      selectedChartOverlapInclusion R a b := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem selectedChartOverlapToProduct_snd :
    selectedChartOverlapToProduct R a b ≫ pullback.snd _ _ =
      selectedChartOverlapMap R a b := pullback.lift_snd _ _ _

theorem selectedChartOverlapToProduct_eq :
    selectedChartOverlapToProduct R a b =
      Spec.map (CommRingCat.ofHom (selectedOverlapTensorCoordinates R a b).toRingHom) ≫
        (pullbackSpecIso R (MvPolynomial (Fin d × Fin (n-d)) R)
          (MvPolynomial (Fin d × Fin (n-d)) R)).inv := by
  apply pullback.hom_ext
  · rw [selectedChartOverlapToProduct_fst]
    dsimp only [selectedChartToSpec]
    rw [Category.assoc, pullbackSpecIso_inv_fst,
      ← Spec.map_comp]
    unfold selectedChartOverlapInclusion
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    change algebraMap _ (Localization.Away (selectedPolynomialBlock R a b).det) p =
      selectedOverlapTensorCoordinates R a b (p ⊗ₜ[R] 1)
    simp [selectedOverlapTensorCoordinates]
  · rw [selectedChartOverlapToProduct_snd]
    dsimp only [selectedChartToSpec]
    rw [Category.assoc, pullbackSpecIso_inv_snd,
      ← Spec.map_comp]
    unfold selectedChartOverlapMap matrixOverlapMap
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    change matrixOverlapCoordinates R (selectedPolynomialBlock R a b)
      (remainingPolynomialBlock R a b) p =
        selectedOverlapTensorCoordinates R a b (1 ⊗ₜ[R] p)
    simp [selectedOverlapTensorCoordinates]

instance selectedChartOverlapToProduct_isClosedImmersion :
    IsClosedImmersion (selectedChartOverlapToProduct R a b) := by
  rw [selectedChartOverlapToProduct_eq]
  have : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (selectedOverlapTensorCoordinates R a b).toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ (selectedOverlapTensorCoordinates_surjective R a b)
  infer_instance

end FlagVarieties.Foundations.QuotientCharts
