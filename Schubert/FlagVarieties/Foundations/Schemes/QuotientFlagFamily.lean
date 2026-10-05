import Schubert.FlagVarieties.Foundations.Schemes.CoordinateLocalFramesPullback
import Schubert.FlagVarieties.Foundations.Schemes.CoordinateQuotientPullbackComparison

/-!
# Families of quotient-sheaf flags

Each step is an epimorphism from the same labelled free sheaf to a locally
free target of its prescribed quotient rank. Adjacent factor maps preserve
the original source and therefore impose the required direction of kernel
incidence without using points or reducedness.
-/

noncomputable section
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- A complete flag as a chain of locally free quotient sheaves. -/
structure QuotientFlagFamily (X : Scheme.{u}) (n : ℕ) where
  /-- The quotient sheaf of step `j`, locally free of rank `n - j`. -/
  target : Fin (n+1) → X.Modules
  /-- The quotient map `𝒪ⁿ ⟶ target j`. -/
  quotient : (j : Fin (n+1)) → coordinateFreeSheaf X n ⟶ target j
  quotient_epi : ∀ j, Epi (quotient j)
  local_frames : ∀ (j : Fin (n+1)) (x : X),
    ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((target j).over U ≅
        SheafOfModules.free (R := X.ringCatSheaf.over U)
          (CoordinateIndex.{u} (n-j.val)))
  /-- The map between consecutive quotients, compatible with the quotient maps. -/
  transition : (j : Fin n) → target j.castSucc ⟶ target j.succ
  transition_source : ∀ j : Fin n,
    quotient j.castSucc ≫ transition j = quotient j.succ

namespace QuotientFlagFamily

variable {X : Scheme.{u}} {n : ℕ} (F : QuotientFlagFamily X n)

/-- Adjacent kernels are incident as sheaf maps. -/
theorem adjacent_kernel_vanish (j : Fin n) :
    kernel.ι (F.quotient j.castSucc) ≫ F.quotient j.succ = 0 := by
  rw [← F.transition_source j, ← Category.assoc, kernel.condition, zero_comp]

end QuotientFlagFamily
end FlagVarieties.Foundations.QuotientCharts
