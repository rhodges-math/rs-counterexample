import RSCounterexample.FlagVarieties.Foundations.Schemes.AffineSheafLocalProjective

/-!
# Finite projectivity and rank from principal coordinate frames

This extends the rank-one section argument to every finite rank, including
zero. The frames are of sections of the given quasicoherent sheaf;
the affine module is its global-section module. Localization descent
proves finite projectivity rather than taking it as an input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory TensorProduct TopologicalSpace QuotientPair
universe u
variable {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent]
  (d : ℕ) (s : Set R)
  (hcover : IsOpenCover (fun g : s => PrimeSpectrum.basicOpen (g : R)))
  (frame : ∀ g : s, Γ(M, PrimeSpectrum.basicOpen (g : R)) ≃ₗ[PrincipalRing (g : R)]
    (Fin d → PrincipalRing (g : R)))

include hcover frame

theorem sheafGlobal_finitePresentation_of_principal_coordinate_frames :
    Module.FinitePresentation R (sheafGlobalModule M) := by
  apply Module.FinitePresentation.of_localizationSpan' s (principalFrame_span_top s hcover)
    (Rₚ := fun g : s => PrincipalRing (g : R))
    (fun g : s => sheafToPrincipal M (g : R))
  intro g
  let := Module.Finite.equiv (frame g).symm
  let := Module.Projective.of_equiv (frame g).symm
  exact Module.finitePresentation_of_projective _ _

theorem sheafGlobal_flat_of_principal_coordinate_frames :
    Module.Flat R (sheafGlobalModule M) := by
  apply Module.flat_of_isLocalized_span (R := R) R (sheafGlobalModule M) s
    (principalFrame_span_top s hcover)
    (fun g : s => Γ(M, PrimeSpectrum.basicOpen (g : R)))
    (fun g : s => sheafToPrincipal M (g : R))
  intro g
  let := IsLocalization.flat (PrincipalRing (g : R)) (Submonoid.powers (g : R))
  let := Module.Projective.of_equiv (frame g).symm
  exact Module.Flat.trans R (PrincipalRing (g : R)) _

theorem sheafGlobal_projective_of_principal_coordinate_frames :
    Module.Projective R (sheafGlobalModule M) := by
  let := sheafGlobal_finitePresentation_of_principal_coordinate_frames M d s hcover frame
  let := sheafGlobal_flat_of_principal_coordinate_frames M d s hcover frame
  exact Module.Flat.projective_of_finitePresentation

theorem sheafGlobal_finite_of_principal_coordinate_frames :
    Module.Finite R (sheafGlobalModule M) := by
  let := sheafGlobal_finitePresentation_of_principal_coordinate_frames M d s hcover frame
  infer_instance

/-- Every stalk has the prescribed finite rank, measured in the
global-section module of the sheaf. -/
theorem sheafGlobal_rank_of_principal_coordinate_frames (p : PrimeSpectrum R) :
    Module.rankAtStalk (sheafGlobalModule M) p = d := by
  have hp : p ∈ ⨆ g : s, PrimeSpectrum.basicOpen (g : R) := by rw [hcover]; trivial
  obtain ⟨g, hg⟩ := Opens.mem_iSup.mp hp
  obtain ⟨p', hp'⟩ :
      p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (PrincipalRing (g : R)))) := by
    rw [PrimeSpectrum.localization_away_comap_range (PrincipalRing (g : R)) (g : R)]
    exact hg
  let := sheafGlobal_finite_of_principal_coordinate_frames M d s hcover frame
  let := sheafGlobal_projective_of_principal_coordinate_frames M d s hcover frame
  let : Nontrivial (PrincipalRing (g : R)) := p'.nontrivial
  rw [← hp', ← Module.rankAtStalk_isBaseChange
    (IsLocalizedModule.isBaseChange (Submonoid.powers (g : R)) (PrincipalRing (g : R))
      (sheafToPrincipal M (g : R))) p', Module.rankAtStalk_eq_of_equiv (frame g),
    Module.rankAtStalk_eq_finrank_of_free]
  simp

end FlagVarieties.Foundations.QuotientCharts
