import Schubert.FlagVarieties.Foundations.Schemes.AffineQuotientFlagRing

/-!
# Recovering every original affine quotient sheaf from its ring flag

The ring flag records precisely the kernels of the original labelled
quotient maps. At each step, the existing coordinate quotient sheaf is
isomorphic to the given target, and the isomorphism preserves the
source morphism rather than only its kernel or its rank.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u

namespace QuotientFlagFamily

variable (A : CommRingCat.{u}) {n : ℕ} (F : QuotientFlagFamily (Spec A) n)

@[simp]
theorem toRingFlag_step (j : Fin (n+1)) :
    (F.toRingFlag A).step j = F.affineStep A j := rfl

theorem toRingFlag_step_submodule (j : Fin (n+1)) :
    ((F.toRingFlag A).step j).toSubmodule =
      LinearMap.ker (affineCoordinateQuotientMap A (F.quotient j)) :=
  F.affineStep_submodule A j

/-- Recovery of the `j`-th sheaf target from its coordinate kernel. -/
def affineStepSheafIso (j : Fin (n+1)) :
    coordinateQuotientSheaf A ((F.toRingFlag A).step j) ≅ F.target j := by
  letI : Epi (F.quotient j) := F.quotient_epi j
  exact affineLocallyFreeGrassmannianSheafIso A (F.quotient j)
    (n-j.val) (F.local_frames j)

/-- Recovery preserves the original rank-`n` labelled source quotient. -/
@[reassoc]
theorem affineStepSheafIso_source (j : Fin (n+1)) :
    coordinateQuotientSheafMap A ((F.toRingFlag A).step j) ≫
      (F.affineStepSheafIso A j).hom = F.quotient j := by
  letI : Epi (F.quotient j) := F.quotient_epi j
  exact affineLocallyFreeGrassmannianSheafIso_source A (F.quotient j)
    (n-j.val) (F.local_frames j)

end QuotientFlagFamily
end FlagVarieties.Foundations.QuotientCharts
