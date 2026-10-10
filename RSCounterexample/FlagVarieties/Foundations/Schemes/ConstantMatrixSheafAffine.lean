import RSCounterexample.FlagVarieties.Foundations.Schemes.ConstantMatrixSheafNaturality
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedSheafBaseChangeCoordinates
import RSCounterexample.FlagVarieties.Foundations.Schemes.AffineCoordinateSheafQuotient
import RSCounterexample.FlagVarieties.Foundations.Flags.RingMatrixFlag

/-! Affine normalization of the constant-matrix free-sheaf action. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u

variable (R : Type u) [CommRing R] {n : ℕ}
  (L : Matrix (Fin n) (Fin n) R) (hL : IsUnit L)

theorem constantMatrixSpecIso_hom_eq_coordinateSheafMap :
    (constantMatrixSpecIso R L hL).hom =
      coordinateSheafMap (CommRingCat.of R) (L.toLinearEquiv' hL.invertible).toLinearMap := by
  rfl

/-- On an affine `R`-scheme, the constant action is the entrywise
specialized matrix action in the original labelled coordinates. -/
theorem constantMatrixSheafIso_specMap_hom
    (A : Type u) [CommRing A] [Algebra R A] :
    (constantMatrixSheafIso R
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) L hL).hom =
    (constantMatrixSpecIso A (L.map (algebraMap R A))
      (RingFlag.matrixBaseChange_isUnit L hL)).hom := by
  let k : CommRingCat.of R ⟶ CommRingCat.of A := CommRingCat.ofHom (algebraMap R A)
  have hc : ∀ i j : Fin n,
      k ((L.toLinearEquiv' hL.invertible).toLinearMap (Pi.single i 1) j) =
      (((L.map (algebraMap R A)).toLinearEquiv'
        (RingFlag.matrixBaseChange_isUnit L hL).invertible).toLinearMap
          (Pi.single i 1)) j := by
    intro i j
    simp [Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Pi.single_apply, k]
  have hp := coordinateSheafMap_pullback k
    (L.toLinearEquiv' hL.invertible).toLinearMap
    ((L.map (algebraMap R A)).toLinearEquiv'
      (RingFlag.matrixBaseChange_isUnit L hL).invertible).toLinearMap hc
  rw [← constantMatrixSpecIso_hom_eq_coordinateSheafMap R L hL,
    ← constantMatrixSpecIso_hom_eq_coordinateSheafMap A (L.map (algebraMap R A))
      (RingFlag.matrixBaseChange_isUnit L hL)] at hp
  dsimp only [k] at hp
  unfold constantMatrixSheafIso
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  apply (cancel_epi (coordinatePullbackIso
    (Spec.map (CommRingCat.ofHom (algebraMap R A))) n).hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hp

end FlagVarieties.Foundations.QuotientCharts
