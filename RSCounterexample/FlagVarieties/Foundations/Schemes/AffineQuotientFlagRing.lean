import RSCounterexample.FlagVarieties.Foundations.Schemes.QuotientFlagFamilyInitial
import RSCounterexample.FlagVarieties.Foundations.Schemes.QuotientFlagFamilyEndpoints
import RSCounterexample.FlagVarieties.Foundations.Schemes.AffineLocallyFreeCoordinateQuotient
import RSCounterexample.FlagVarieties.Foundations.Flags.Ring

/-!
# The ring flag of an affine quotient-sheaf flag

Every step uses the original epimorphism of labelled free sheaves and its
affine section kernel. Adjacent source-preserving sheaf factors
induce inclusion of these kernels. The zero and full endpoints
come from the previously derived sheaf endpoint theorems.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits QuotientPair
universe u

namespace QuotientFlagFamily

variable (A : CommRingCat.{u}) {n : ℕ} (F : QuotientFlagFamily (Spec A) n)

/-- The existing affine Grassmannian construction applied to one
quotient-sheaf step. -/
def affineStep (j : Fin (n+1)) : Module.Grassmannian A (Fin n → A) (n-j.val) := by
  letI : Epi (F.quotient j) := F.quotient_epi j
  exact affineLocallyFreeGrassmannian A (F.quotient j) (n-j.val) (F.local_frames j)

theorem affineStep_submodule (j : Fin (n+1)) :
    (F.affineStep A j).toSubmodule =
      LinearMap.ker (affineCoordinateQuotientMap A (F.quotient j)) := by
  unfold affineStep affineLocallyFreeGrassmannian affineCoordinateGrassmannian
  rfl

/-- Adjacent sheaf factors force inclusion of the original affine
coordinate kernels, over arbitrary coefficient rings. -/
theorem affineStep_adjacent (j : Fin n) :
    (F.affineStep A j.castSucc).toSubmodule ≤
      (F.affineStep A j.succ).toSubmodule := by
  rw [F.affineStep_submodule A, F.affineStep_submodule A]
  have hlin :
      (moduleSpecΓFunctor.map (F.transition j)).hom.comp
        (affineCoordinateQuotientMap A (F.quotient j.castSucc)) =
      affineCoordinateQuotientMap A (F.quotient j.succ) := by
    apply LinearMap.ext
    intro v
    have h := congrArg (fun q => moduleSpecΓFunctor.map q) (F.transition_source j)
    simp only [Functor.map_comp] at h
    exact congrArg (fun q => q.hom ((coordinateFreeGlobalIso A n).hom v)) h
  intro v hv
  change affineCoordinateQuotientMap A (F.quotient j.succ) v = 0
  rw [← hlin]
  simp only [LinearMap.comp_apply, LinearMap.mem_ker.mp hv, map_zero]

/-- The initial kernel is zero because the first sheaf quotient
is an isomorphism. -/
theorem affineStep_zero : (F.affineStep A 0).toSubmodule = ⊥ := by
  rw [F.affineStep_submodule A, LinearMap.ker_eq_bot]
  haveI : IsIso (F.quotient 0) := F.initial_quotient_isIso
  haveI : IsIso (moduleSpecΓFunctor.map (F.quotient 0)) := inferInstance
  exact (ConcreteCategory.bijective_of_isIso (moduleSpecΓFunctor.map (F.quotient 0))).1.comp
    (ConcreteCategory.bijective_of_isIso (coordinateFreeGlobalIso A n).hom).1

/-- The final kernel is the whole labelled source because its
target sheaf is zero. -/
theorem affineStep_last : (F.affineStep A (Fin.last n)).toSubmodule = ⊤ := by
  rw [F.affineStep_submodule A, LinearMap.ker_eq_top]
  letI : (moduleSpecΓFunctor (R := A)).IsRightAdjoint :=
    ⟨tilde.functor A, ⟨tilde.adjunction (R := A)⟩⟩
  have hz : IsZero (moduleSpecΓFunctor.obj (F.target (Fin.last n))) :=
    (F.last_target_isZero.isTerminal.isTerminalObj moduleSpecΓFunctor _).isZero
  letI : Subsingleton (sheafGlobalModule (F.target (Fin.last n))) :=
    ModuleCat.subsingleton_of_isZero hz
  apply LinearMap.ext
  intro v
  exact Subsingleton.elim _ _

/-- The affine sheaf family gives the existing ring-valued flag,
with its original coordinate kernels and both endpoints. -/
def toRingFlag : RingFlag A (Fin n → A) n where
  step := F.affineStep A
  step_mono := by
    apply Fin.monotone_iff_le_succ.mpr
    exact F.affineStep_adjacent A
  step_zero := F.affineStep_zero A
  step_last := F.affineStep_last A

end QuotientFlagFamily
end FlagVarieties.Foundations.QuotientCharts
