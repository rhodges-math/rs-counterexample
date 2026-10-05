import Schubert.FlagVarieties.Foundations.Flags.RingBasisFlag
import Schubert.FlagVarieties.Foundations.Schemes.SimultaneousFlagCoordinateBaseChange
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Scalar extension of a basis flag in its original coordinates -/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

open Module TensorProduct

universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {n : ℕ}

/-- Extend every basis column by the given coefficient map. -/
def coordinateBasisBaseChange (b : Basis (Fin n) A (Fin n → A)) :
    Basis (Fin n) B (Fin n → B) :=
  (b.baseChange B).map (TensorProduct.piScalarRight A B B (Fin n))

@[simp] theorem coordinateBasisBaseChange_apply
    (b : Basis (Fin n) A (Fin n → A)) (i j : Fin n) :
    coordinateBasisBaseChange (B := B) b i j = algebraMap A B (b i j) := by
  simp [coordinateBasisBaseChange, TensorProduct.piScalarRight_apply, Algebra.smul_def]

/-- Arbitrary scalar extension carries a prefix span to the same prefix of
the extended columns. No flatness or nontriviality assumption is needed. -/
theorem coordinateRingFlagBaseChange_ofBasis
    (b : Basis (Fin n) A (Fin n → A)) :
    coordinateRingFlagBaseChange (B := B) (RingFlag.ofBasis b) =
      RingFlag.ofBasis (coordinateBasisBaseChange (B := B) b) := by
  apply RingFlag.ext
  intro j
  rw [coordinateRingFlagBaseChange_step, coordinateGrassmannianBaseChange_submodule,
    RingFlag.ofBasis_step_span, RingFlag.ofBasis_step_span,
    Submodule.baseChange_span, Submodule.map_span]
  congr 1
  rw [Set.image_image, Set.image_image]
  congr 1
  funext i
  ext t
  simp [coordinateBasisBaseChange_apply, TensorProduct.piScalarRight_apply, Algebra.smul_def]

/-- A chosen adapted basis remains adapted after every coefficient extension. -/
theorem coordinateBasisBaseChange_adapted (F : RingFlag A (Fin n → A) n)
    (b : Basis (Fin n) A (Fin n → A))
    (hb : ∀ j, (F.step j).toSubmodule =
      Submodule.span A (b '' {i | i.val < j.val})) (j : Fin (n + 1)) :
    ((coordinateRingFlagBaseChange (B := B) F).step j).toSubmodule =
      Submodule.span B (coordinateBasisBaseChange (B := B) b '' {i | i.val < j.val}) := by
  rw [← RingFlag.ofBasis_eq_of_adapted F b hb, coordinateRingFlagBaseChange_ofBasis]
  rfl

end FlagVarieties.Foundations.QuotientCharts
