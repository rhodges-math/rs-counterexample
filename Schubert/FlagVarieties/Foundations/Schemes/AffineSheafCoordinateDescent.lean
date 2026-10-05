import Schubert.FlagVarieties.Foundations.Schemes.AffineSheafCoordinateFrames

/-!
# Finite projectivity from sheaf frames on principal opens

The local hypotheses are sheaf isomorphisms. Quasicoherence, finite
projectivity of global sections, and constant stalk rank are conclusions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory TopologicalSpace QuotientPair
universe u
variable {R : CommRingCat.{u}} (M : (Spec R).Modules) (d : ℕ) (s : Set R)
  (hcover : IsOpenCover (fun g : s => PrimeSpectrum.basicOpen (g : R)))
  (e : ∀ g : s, M.over (PrimeSpectrum.basicOpen (g : R)) ≅
    SheafOfModules.free
      (R := (Spec R).ringCatSheaf.over (PrimeSpectrum.basicOpen (g : R)))
      (CoordinateIndex.{u} d))

include hcover e

theorem isQuasicoherent_of_principal_coordinate_sheaf_frames : M.IsQuasicoherent := by
  let (g : s) : (M.over (PrimeSpectrum.basicOpen (g : R))).IsQuasicoherent := by
    let S := (Spec R).ringCatSheaf.over (PrimeSpectrum.basicOpen (g : R))
    exact (SheafOfModules.isQuasicoherent S).prop_of_iso (e g).symm inferInstance
  apply SheafOfModules.IsQuasicoherent.of_coversTop M
    (fun g : s => PrimeSpectrum.basicOpen (g : R))
  simpa only [Opens.coversTop_iff] using hcover

theorem finite_projective_of_principal_coordinate_sheaf_frames :
    Module.Finite R (sheafGlobalModule M) ∧ Module.Projective R (sheafGlobalModule M) := by
  let := isQuasicoherent_of_principal_coordinate_sheaf_frames M d s hcover e
  let frames := fun g : s => overCoordinateSectionFrame M _ d (e g)
  exact ⟨sheafGlobal_finite_of_principal_coordinate_frames M d s hcover frames,
    sheafGlobal_projective_of_principal_coordinate_frames M d s hcover frames⟩

theorem rank_of_principal_coordinate_sheaf_frames (p : PrimeSpectrum R) :
    Module.rankAtStalk (sheafGlobalModule M) p = d := by
  let := isQuasicoherent_of_principal_coordinate_sheaf_frames M d s hcover e
  exact sheafGlobal_rank_of_principal_coordinate_frames M d s hcover
    (fun g : s => overCoordinateSectionFrame M _ d (e g)) p

end FlagVarieties.Foundations.QuotientCharts
