import RSCounterexample.FlagVarieties.Foundations.Schemes.QuotientFlagFamily

/-!
# Pullback of quotient-sheaf flags

The labelled quotient maps and adjacent factor maps are pulled back
along an arbitrary scheme morphism. Pointwise fixed-rank frames pull back
to inverse-image opens; no flatness or generic kernel-exactness premise is
used.
-/

noncomputable section
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u

namespace QuotientFlagFamily

variable {X Y : Scheme.{u}} {n : ℕ}

/-- Pull back every quotient and adjacent source-preserving factor. -/
def pullback (f : X ⟶ Y) (F : QuotientFlagFamily Y n) :
    QuotientFlagFamily X n where
  target j := (Scheme.Modules.pullback f).obj (F.target j)
  quotient j := coordinatePullbackQuotient f (F.quotient j)
  quotient_epi j := by
    let : Epi (F.quotient j) := F.quotient_epi j
    infer_instance
  local_frames j :=
    FlagVarieties.Foundations.ModuleSheafGluing.coordinateLocalFrames_pullback f
      (F.target j) (n-j.val) (F.local_frames j)
  transition j := (Scheme.Modules.pullback f).map (F.transition j)
  transition_source j := by
    rw [coordinatePullbackQuotient_map_target, F.transition_source]

@[simp]
theorem pullback_quotient (f : X ⟶ Y) (F : QuotientFlagFamily Y n)
    (j : Fin (n+1)) :
    (F.pullback f).quotient j = coordinatePullbackQuotient f (F.quotient j) := rfl

@[simp]
theorem pullback_transition (f : X ⟶ Y) (F : QuotientFlagFamily Y n)
    (j : Fin n) :
    (F.pullback f).transition j = (Scheme.Modules.pullback f).map (F.transition j) := rfl

end QuotientFlagFamily
end FlagVarieties.Foundations.QuotientCharts
