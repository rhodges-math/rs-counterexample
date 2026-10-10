import RSCounterexample.FlagVarieties.Foundations.Schemes.ConstantMatrixSheaf
import RSCounterexample.FlagVarieties.Foundations.Schemes.QuotientFlagFamily

/-! Transport the quotient-chain source by a constant invertible matrix. -/

noncomputable section
set_option linter.style.haveILetI false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory

universe u

namespace QuotientFlagFamily

variable (R : Type u) [CommRing R] {X : Scheme.{u}} {n : ℕ}
  (b : X ⟶ Spec (CommRingCat.of R))
  (L : Matrix (Fin n) (Fin n) R) (hL : IsUnit L)

/-- Precompose each original quotient with the inverse of the
constant matrix action. The kernels therefore move by `L`, while every
target, local frame and adjacent factor remains the original one. -/
def matrixTransport (F : QuotientFlagFamily X n) : QuotientFlagFamily X n where
  target := F.target
  quotient j := (constantMatrixSheafIso R b L hL).inv ≫ F.quotient j
  quotient_epi j := by
    letI : Epi (F.quotient j) := F.quotient_epi j
    infer_instance
  local_frames := F.local_frames
  transition := F.transition
  transition_source j := by
    rw [Category.assoc, F.transition_source j]

@[simp] theorem matrixTransport_target (F : QuotientFlagFamily X n)
    (j : Fin (n+1)) :
    (F.matrixTransport R b L hL).target j = F.target j := rfl

@[simp] theorem matrixTransport_quotient (F : QuotientFlagFamily X n)
    (j : Fin (n+1)) :
    (F.matrixTransport R b L hL).quotient j =
      (constantMatrixSheafIso R b L hL).inv ≫ F.quotient j := rfl

@[simp] theorem matrixTransport_transition (F : QuotientFlagFamily X n)
    (j : Fin n) :
    (F.matrixTransport R b L hL).transition j = F.transition j := rfl

end QuotientFlagFamily
end FlagVarieties.Foundations.QuotientCharts
