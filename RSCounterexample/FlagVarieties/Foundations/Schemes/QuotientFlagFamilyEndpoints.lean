import RSCounterexample.FlagVarieties.Foundations.Schemes.QuotientFlagFamily
import RSCounterexample.FlagVarieties.Foundations.Schemes.ModuleSheafLocalQuotientComparison

/-!
# The rank-zero endpoint of a quotient-sheaf flag

Pointwise local frames of rank zero force the final target to be the zero
sheaf globally. The proof detects equality of the identity and zero maps
on an open cover; no endpoint assumption is stored in the family.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace QuotientFlagFamily

variable {X : Scheme.{u}} {n : ℕ} (F : QuotientFlagFamily X n)

/-- The last quotient target is the zero sheaf, derived only from
its pointwise local rank-zero frames. -/
theorem last_target_isZero : IsZero (F.target (Fin.last n)) := by
  let M := F.target (Fin.last n)
  let I := {U : X.Opens // Nonempty (M.over U ≅
    SheafOfModules.free (R := X.ringCatSheaf.over U) (CoordinateIndex.{u} 0))}
  let U : I → X.Opens := fun i => i.1
  have hcover : ∀ x : X, ∃ i : I, x ∈ U i := by
    intro x
    obtain ⟨V, hx, hframe⟩ := F.local_frames (Fin.last n) x
    have hframe' : Nonempty (M.over V ≅
        SheafOfModules.free (R := X.ringCatSheaf.over V)
          (CoordinateIndex.{u} 0)) := by
      simpa [M] using hframe
    exact ⟨⟨V, hframe'⟩, hx⟩
  apply (IsZero.iff_id_eq_zero M).mpr
  apply FlagVarieties.Foundations.ModuleSheafGluing.hom_ext_of_over U hcover
  intro i
  obtain ⟨e⟩ := i.2
  have hzfree : IsZero (SheafOfModules.free
      (R := X.ringCatSheaf.over (U i)) (CoordinateIndex.{u} 0)) := by
    apply IsInitial.isZero
    apply IsInitial.ofUniqueHom (fun N => 0)
    intro N f
    apply (SheafOfModules.freeHomEquiv N).injective
    funext j
    exact Fin.elim0 j.down
  have hz : IsZero (M.over (U i)) := e.isZero_iff.mpr hzfree
  exact hz.eq_of_src _ _

end QuotientFlagFamily
end FlagVarieties.Foundations.QuotientCharts
