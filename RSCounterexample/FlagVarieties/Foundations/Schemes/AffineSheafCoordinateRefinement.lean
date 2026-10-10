import RSCounterexample.FlagVarieties.Foundations.Schemes.AffineSheafCoordinateDescent

/-!
# Principal refinement of finite-rank local trivializations

All local frames are isomorphisms of the module sheaf. The affine
principal basis supplies the cover used to derive the finite projective
global-section module; no principal cover is part of the input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory TopologicalSpace QuotientPair
universe u

/-- Restrict a coordinate frame along an open inclusion. -/
def restrictOverCoordinateFrame {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens}
    (h : V ≤ U) (d : ℕ)
    (e : M.over U ≅
      SheafOfModules.free (R := X.ringCatSheaf.over U) (CoordinateIndex.{u} d)) :
    M.over V ≅
      SheafOfModules.free (R := X.ringCatSheaf.over V) (CoordinateIndex.{u} d) :=
  ((SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE h)).app M).symm ≪≫
    (SheafOfModules.overMap X.ringCatSheaf (homOfLE h)).mapIso
      (e ≪≫ (ModuleSheafGluing.coordinateOverFreeIso U d).symm) ≪≫
    (SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE h)).app
      (coordinateFreeSheaf X d) ≪≫ ModuleSheafGluing.coordinateOverFreeIso V d

variable {R : CommRingCat.{u}} (M : (Spec R).Modules) (d : ℕ)
  (hfree : ∀ p : Spec R, ∃ U : (Spec R).Opens, p ∈ U ∧
    Nonempty (M.over U ≅
      SheafOfModules.free (R := (Spec R).ringCatSheaf.over U) (CoordinateIndex.{u} d)))

include hfree

theorem exists_principal_coordinate_sheaf_frames :
    ∃ s : Set R,
      IsOpenCover (fun g : s => PrimeSpectrum.basicOpen (g : R)) ∧
      Nonempty (∀ g : s, M.over (PrimeSpectrum.basicOpen (g : R)) ≅
        SheafOfModules.free
          (R := (Spec R).ringCatSheaf.over (PrimeSpectrum.basicOpen (g : R)))
          (CoordinateIndex.{u} d)) := by
  let s : Set R := {g | Nonempty (M.over (PrimeSpectrum.basicOpen g) ≅
    SheafOfModules.free (R := (Spec R).ringCatSheaf.over (PrimeSpectrum.basicOpen g))
      (CoordinateIndex.{u} d))}
  refine ⟨s, ?_, ⟨fun g => g.property.some⟩⟩
  apply top_le_iff.mp
  intro p hp
  obtain ⟨U, hpU, ⟨e⟩⟩ := hfree p
  obtain ⟨a, ⟨_, ⟨g, rfl⟩, rfl⟩, hpg, hgU : PrimeSpectrum.basicOpen g ≤ U⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hpU U.2
  exact Opens.mem_iSup.mpr ⟨⟨g, ⟨restrictOverCoordinateFrame M hgU d e⟩⟩, hpg⟩

theorem locally_coordinate_trivial_isQuasicoherent : M.IsQuasicoherent := by
  obtain ⟨s, hs, ⟨e⟩⟩ := exists_principal_coordinate_sheaf_frames M d hfree
  exact isQuasicoherent_of_principal_coordinate_sheaf_frames M d s hs e

theorem locally_coordinate_trivial_finite_projective :
    Module.Finite R (sheafGlobalModule M) ∧ Module.Projective R (sheafGlobalModule M) := by
  obtain ⟨s, hs, ⟨e⟩⟩ := exists_principal_coordinate_sheaf_frames M d hfree
  exact finite_projective_of_principal_coordinate_sheaf_frames M d s hs e

theorem locally_coordinate_trivial_rank (p : PrimeSpectrum R) :
    Module.rankAtStalk (sheafGlobalModule M) p = d := by
  obtain ⟨s, hs, ⟨e⟩⟩ := exists_principal_coordinate_sheaf_frames M d hfree
  exact rank_of_principal_coordinate_sheaf_frames M d s hs e p

end FlagVarieties.Foundations.QuotientCharts
