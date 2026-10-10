import RSCounterexample.FlagVarieties.Foundations.Schemes.QuotientSheafFrameTransitions

/-!
# Constructed affine frame covers for line sheaves

Each point's local sheaf trivialization is restricted to an
affine neighborhood. Thus the affine cover, frames, and
quasicoherence used by the projective-map gluing are consequences of
local line-sheaf triviality.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientPair

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

variable {X : Scheme.{u}} (N : X.Modules)

/-- An affine neighborhood and sheaf frame at each point. -/
structure AffineSheafFrameCover where
  /-- An affine open neighborhood of each point. -/
  opens : X → X.Opens
  mem : ∀ x, x ∈ opens x
  affine : ∀ x, IsAffineOpen (opens x)
  /-- A trivialization of the sheaf over each chosen neighborhood. -/
  frame : ∀ x, N.over (opens x) ≅ SheafOfModules.unit (X.ringCatSheaf.over (opens x))

theorem AffineSheafFrameCover.isOpenCover (D : AffineSheafFrameCover N) :
    IsOpenCover D.opens := by
  apply top_le_iff.mp
  intro x hx
  exact Opens.mem_iSup.mpr ⟨x, D.mem x⟩

/-- The affine neighborhoods and their frames are constructed from local line-sheaf isomorphisms. -/
theorem exists_affineSheafFrameCover
    (hline : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))) :
    Nonempty (AffineSheafFrameCover N) := by
  have h (x : X) : ∃ V : X.Opens, x ∈ V ∧ IsAffineOpen V ∧
      Nonempty (N.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V)) := by
    obtain ⟨U, hx, ⟨e⟩⟩ := hline x
    obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hx
    exact ⟨V, hxV, hV, ⟨restrictOverSheafFrame N hVU e⟩⟩
  choose V hmem haff hframe using h
  exact ⟨⟨V, hmem, haff, fun x => (hframe x).some⟩⟩

/-- A chosen affine frame cover of a sheaf that is locally isomorphic to the structure sheaf. -/
def chooseAffineSheafFrameCover
    (hline : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))) :
    AffineSheafFrameCover N :=
  (exists_affineSheafFrameCover N hline).some

/-- Quasicoherence is derived from local sheaf isomorphisms on the constructed cover. -/
theorem quotientLineSheaf_isQuasicoherent
    (hline : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))) :
    N.IsQuasicoherent := by
  let D := chooseAffineSheafFrameCover N hline
  let (x : X) : (N.over (D.opens x)).IsQuasicoherent := by
    let S := X.ringCatSheaf.over (D.opens x)
    let eu : SheafOfModules.free (R := S) (ULift.{u} Unit) ≅ SheafOfModules.unit S :=
      coproductUniqueIso (fun _ : ULift.{u} Unit => SheafOfModules.unit S)
    exact (SheafOfModules.isQuasicoherent S).prop_of_iso (eu ≪≫ (D.frame x).symm) inferInstance
  apply SheafOfModules.IsQuasicoherent.of_coversTop N D.opens
  simpa only [Opens.coversTop_iff] using D.isOpenCover

end FlagVarieties.Foundations.QuotientPair
