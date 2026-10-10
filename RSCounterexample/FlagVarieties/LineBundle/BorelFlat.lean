import RSCounterexample.FlagVarieties.LineBundle.Density
import Mathlib.RingTheory.Flat.Localization

/-!
# `𝒪(B)` is flat over the base

For every commutative ring `R`, the coordinate ring `𝒪(B)` of the Borel subgroup is a retract of
the localization `R[xᵢⱼ][(∏ xᵢᵢ)⁻¹]` of a polynomial ring (`FlagVarieties.fromUpperRing` is a
left inverse of `FlagVarieties.toUpperRing`), hence flat over `R`
(`FlagVarieties.instFlatBorelCoord`).
-/

noncomputable section

namespace FlagVarieties

open MvPolynomial

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

theorem isUnit_aeval_diagProd :
    IsUnit (aeval (fun ij : Fin n × Fin n => borelMatrix R n ij.1 ij.2) (diagProd R n)) := by
  rw [diagProd, map_prod]
  simp only [aeval_X]
  rw [← Matrix.det_of_isUpperTriangular (borelMatrix_blockTriangular R n)]
  exact isUnit_det_borelMatrix R n

/-- `R[xᵢⱼ][(∏ xᵢᵢ)⁻¹] → 𝒪(B)`, `xᵢⱼ ↦ bᵢⱼ` (which is `0` below the diagonal). -/
def fromUpperRing : UpperRing R n →ₐ[R] BorelCoord R n :=
  IsLocalization.Away.liftAlgHom (diagProd R n)
    (f := aeval fun ij : Fin n × Fin n => borelMatrix R n ij.1 ij.2) (isUnit_aeval_diagProd R n)

theorem fromUpperRing_algebraMap (p : MvPolynomial (Fin n × Fin n) R) :
    fromUpperRing R n (algebraMap _ (UpperRing R n) p) =
      aeval (fun ij : Fin n × Fin n => borelMatrix R n ij.1 ij.2) p := by
  rw [fromUpperRing, IsLocalization.Away.liftAlgHom_apply]
  exact IsLocalization.lift_eq _ _

theorem fromUpperRing_comp_toUpperRing :
    (fromUpperRing R n).comp (toUpperRing R n) = AlgHom.id R (BorelCoord R n) := by
  apply borelMatrix_algHom_ext
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply, AlgHom.comp_apply, AlgHom.id_apply]
  have h := congrFun (congrFun (borelMatrix_map_borelPointOfMatrix R (upperGenericMatrix R n)
    (isUnit_det_upperGenericMatrix R n) (upperGenericMatrix_blockTriangular R n)) i) j
  rw [Matrix.map_apply] at h
  change fromUpperRing R n (borelPointOfMatrix R _ _ _ (borelMatrix R n i j)) = _
  rw [h, upperGenericMatrix, Matrix.of_apply, fromUpperRing_algebraMap]
  split_ifs with hij
  · rw [aeval_X]
  · rw [map_zero]
    exact (borelMatrix_blockTriangular R n (not_le.mp hij)).symm

/-- **`𝒪(B)` is flat over `R`.** -/
instance instFlatBorelCoord : Module.Flat R (BorelCoord R n) :=
  Module.Flat.of_retract (toUpperRing R n).toLinearMap (fromUpperRing R n).toLinearMap
    (LinearMap.ext fun x => by
      change ((fromUpperRing R n).comp (toUpperRing R n)) x = x
      rw [fromUpperRing_comp_toUpperRing, AlgHom.id_apply])

end FlagVarieties
