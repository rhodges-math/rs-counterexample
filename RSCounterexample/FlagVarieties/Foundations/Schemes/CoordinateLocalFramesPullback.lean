import RSCounterexample.FlagVarieties.Foundations.Schemes.ModuleSheafLocalFrames
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedUniversalPullbackFrames

/-!
# Pullback of coordinate local frames

An arbitrary scheme morphism preserves fixed-rank coordinate frames on
open subschemes. The relevant new open is the preimage of the original one.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.ModuleSheafGluing

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open FlagVarieties.Foundations.QuotientCharts

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (d : ℕ)

/-- Convert an over-site frame into a frame on the open subscheme. -/
def coordinateRestrictionFrameOfOver (U : Y.Opens)
    (e : M.over U ≅
      SheafOfModules.free (R := Y.ringCatSheaf.over U) (CoordinateIndex.{u} d)) :
    M.restrict U.ι ≅ coordinateFreeSheaf U.toScheme d :=
  ((Scheme.Modules.overFunctorEquiv U).app M).symm ≪≫
    (Scheme.Modules.overEquiv U).functor.mapIso e ≪≫
    (Scheme.Modules.overEquiv U).functor.mapIso (coordinateOverFreeIso U d).symm ≪≫
    (Scheme.Modules.overFunctorEquiv U).app (coordinateFreeSheaf Y d) ≪≫
    coordinateRestrictFreeIso U.ι d

/-- Base change of a restriction frame to the preimage open. -/
def coordinatePreimageRestrictionFrame (U : Y.Opens)
    (e : M.restrict U.ι ≅ coordinateFreeSheaf U.toScheme d) :
    ((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι ≅
      coordinateFreeSheaf (f ⁻¹ᵁ U).toScheme d :=
  (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app _ ≪≫
    (Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).app M ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (f ∣_ U) U.ι).app M).symm ≪≫
    (Scheme.Modules.pullback (f ∣_ U)).mapIso
      (((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm ≪≫ e) ≪≫
    coordinatePullbackFreeIso (f ∣_ U) d

/-- A frame on an open of the target pulls back to its preimage open. -/
def coordinatePreimageOverFrame (U : Y.Opens)
    (e : M.over U ≅
      SheafOfModules.free (R := Y.ringCatSheaf.over U) (CoordinateIndex.{u} d)) :
    ((Scheme.Modules.pullback f).obj M).over (f ⁻¹ᵁ U) ≅
      SheafOfModules.free (R := X.ringCatSheaf.over (f ⁻¹ᵁ U))
        (CoordinateIndex.{u} d) :=
  coordinateOverFrame ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U) d
    (coordinatePreimageRestrictionFrame f M d U
      (coordinateRestrictionFrameOfOver M d U e))

/-- Pointwise fixed-rank coordinate local freeness survives arbitrary scheme pullback. -/
theorem coordinateLocalFrames_pullback
    (h : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧
      Nonempty (M.over U ≅
        SheafOfModules.free (R := Y.ringCatSheaf.over U) (CoordinateIndex.{u} d))) :
    ∀ x : X, ∃ V : X.Opens, x ∈ V ∧
      Nonempty (((Scheme.Modules.pullback f).obj M).over V ≅
        SheafOfModules.free (R := X.ringCatSheaf.over V) (CoordinateIndex.{u} d)) := by
  intro x
  obtain ⟨U, hxU, ⟨e⟩⟩ := h (f x)
  refine ⟨f ⁻¹ᵁ U, (f.mem_preimage).mpr hxU, ?_⟩
  exact ⟨coordinatePreimageOverFrame f M d U e⟩

end FlagVarieties.Foundations.ModuleSheafGluing
