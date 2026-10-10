import RSCounterexample.FlagVarieties.Foundations.Schemes.ModuleSheafGluingRestriction
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedUniversalChart
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Local frames yield locally free, finite-type module sheaves

Frames on open subschemes are transported to the over site and used to build
Mathlib's local generator data. Thus local freeness and finite type are the
library properties of the sheaf, not separate predicates on charts.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.ModuleSheafGluing

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open FlagVarieties.Foundations.QuotientCharts

universe u

variable {X : Scheme.{u}}

/-- The labelled free sheaf restricts to the same labelled free sheaf on the over site. -/
def coordinateOverFreeIso (U : X.Opens) (d : ℕ) :
    (coordinateFreeSheaf X d).over U ≅
      SheafOfModules.free (R := X.ringCatSheaf.over U) (CoordinateIndex.{u} d) := by
  let F := SheafOfModules.overFunctor.{u} X.ringCatSheaf U
  have : PreservesColimitsOfSize.{u, u} F := by
    dsimp [F, SheafOfModules.overFunctor]
    infer_instance
  exact (SheafOfModules.mapFreeIso F (CoordinateIndex.{u} d) (Iso.refl _)).symm

/-- Convert an open-subscheme frame to a frame on the equivalent over site. -/
def coordinateOverFrame (M : X.Modules) (U : X.Opens) (d : ℕ)
    (e : M.restrict U.ι ≅ coordinateFreeSheaf U.toScheme d) :
    M.over U ≅ SheafOfModules.free (R := X.ringCatSheaf.over U) (CoordinateIndex.{u} d) :=
  restrictionIsoToOver U (e ≪≫ (coordinateRestrictFreeIso U.ι d).symm) ≪≫
    coordinateOverFreeIso U d

variable {I : Type u} (M : X.Modules) (U : I → X.Opens) (d : ℕ)
  (hcover : ∀ x : X, ∃ i, x ∈ U i)
  (frame : ∀ i, M.restrict (U i).ι ≅ coordinateFreeSheaf (U i).toScheme d)

/-- Local generator data obtained from the cover and frames. -/
def localGeneratorsOfFrames : M.LocalGeneratorsData where
  I := I
  X := U
  coversTop := by
    rw [Opens.coversTop_iff, IsOpenCover]
    apply le_antisymm le_top
    intro x _
    exact Opens.mem_iSup.mpr (hcover x)
  generators i :=
    (SheafOfModules.free.generatingSections (CoordinateIndex.{u} d)).ofEpi
      (coordinateOverFrame M (U i) d (frame i)).inv

instance localGeneratorsOfFrames_isLocallyFreeData :
    (localGeneratorsOfFrames M U d hcover frame).IsLocallyFreeData where
  isIso i := by
    change I at i
    change IsIso ((SheafOfModules.free.generatingSections (CoordinateIndex.{u} d)).ofEpi
      (coordinateOverFrame M (U i) d (frame i)).inv).π
    rw [SheafOfModules.GeneratingSections.ofEpi_π,
      SheafOfModules.free.generatingSections_π]
    infer_instance

instance localGeneratorsOfFrames_isFiniteType :
    (localGeneratorsOfFrames M U d hcover frame).IsFiniteType where
  isFiniteType _i := ⟨inferInstanceAs (Finite (CoordinateIndex.{u} d))⟩

include hcover frame

/-- Local freeness in the library sense follows from open-subscheme frames. -/
theorem isLocallyFree_of_frames : M.IsLocallyFree :=
  (localGeneratorsOfFrames M U d hcover frame).isLocallyFree

/-- These same finite frames prove finite type in the library sense. -/
theorem isFiniteType_of_frames : M.IsFiniteType := by
  apply SheafOfModules.IsFiniteType.mk (M := M)
  refine ⟨localGeneratorsOfFrames M U d hcover frame, ?_⟩
  infer_instance

/-- The framed sheaf is quasicoherent, with no affine-base restriction. -/
theorem isQuasicoherent_of_frames : M.IsQuasicoherent := by
  let := isLocallyFree_of_frames M U d hcover frame
  infer_instance

end FlagVarieties.Foundations.ModuleSheafGluing
