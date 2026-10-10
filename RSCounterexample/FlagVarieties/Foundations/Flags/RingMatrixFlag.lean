import RSCounterexample.FlagVarieties.Foundations.Flags.RingBasisBaseChange
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! # The column flag of an invertible matrix over a ring -/

noncomputable section

namespace FlagVarieties.Foundations.RingFlag

open Module Matrix

universe u
variable {A : Type u} [CommRing A] {n : ℕ}

/-- The ordered basis consisting of the matrix columns. -/
def matrixBasis (M : Matrix (Fin n) (Fin n) A) (hM : IsUnit M) :
    Basis (Fin n) A (Fin n → A) :=
  (Pi.basisFun A (Fin n)).map (M.toLinearEquiv' hM.invertible)

@[simp] theorem matrixBasis_apply (M : Matrix (Fin n) (Fin n) A)
    (hM : IsUnit M) (j : Fin n) : matrixBasis M hM j = M.col j := by
  simp only [matrixBasis, Basis.map_apply, Pi.basisFun_apply]
  change M *ᵥ (Pi.single j 1) = M.col j
  exact Matrix.mulVec_single_one M j

/-- Its flag has the initial column spans. -/
def ofMatrix (M : Matrix (Fin n) (Fin n) A) (hM : IsUnit M) :
    RingFlag A (Fin n → A) n := ofBasis (matrixBasis M hM)

theorem ofMatrix_step (M : Matrix (Fin n) (Fin n) A)
    (hM : IsUnit M) (j : Fin (n + 1)) :
    ((ofMatrix M hM).step j).toSubmodule =
      Submodule.span A ((fun i => M.col i) '' {i | i.val < j.val}) := by
  simp only [ofMatrix, ofBasis_step_span, matrixBasis_apply]

variable {B : Type u} [CommRing B] [Algebra A B]

theorem matrixBaseChange_isUnit (M : Matrix (Fin n) (Fin n) A) (hM : IsUnit M) :
    IsUnit (M.map (algebraMap A B)) := by
  exact hM.map (algebraMap A B).mapMatrix

theorem coordinateBasisBaseChange_matrixBasis (M : Matrix (Fin n) (Fin n) A)
    (hM : IsUnit M) :
    QuotientCharts.coordinateBasisBaseChange (B := B) (matrixBasis M hM) =
      matrixBasis (M.map (algebraMap A B)) (matrixBaseChange_isUnit M hM) := by
  apply DFunLike.ext
  intro i
  ext j
  simp

theorem coordinateRingFlagBaseChange_ofMatrix (M : Matrix (Fin n) (Fin n) A)
    (hM : IsUnit M) :
    QuotientCharts.coordinateRingFlagBaseChange (B := B) (ofMatrix M hM) =
      ofMatrix (M.map (algebraMap A B)) (matrixBaseChange_isUnit M hM) := by
  rw [ofMatrix, QuotientCharts.coordinateRingFlagBaseChange_ofBasis,
    coordinateBasisBaseChange_matrixBasis]
  rfl

end FlagVarieties.Foundations.RingFlag
