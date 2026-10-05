import Schubert.FlagVarieties.Foundations.Schemes.AffineQuotientSheafFrame
import Mathlib.RingTheory.LocalProperties.FinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.Localization

/-!
# Finite projectivity from principal section frames

For a quasicoherent sheaf on `Spec R`, a covering family of rank-one
frames of its principal-open section modules implies that its
affine section module is finite projective of stalk rank one.
The tensor/restriction comparison is proved in `AffineSheafSections`;
no finite-projectivity or rank assertion is an input here.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientPair

open AlgebraicGeometry CategoryTheory TensorProduct TopologicalSpace

universe u

variable {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent]
  (s : Set R) (hcover : IsOpenCover (fun g : s => PrimeSpectrum.basicOpen (g : R)))
  (frame : ∀ g : s, Γ(M, PrimeSpectrum.basicOpen (g : R)) ≃ₗ[PrincipalRing (g : R)]
    PrincipalRing (g : R))

include hcover in
theorem principalFrame_span_top : Ideal.span s = ⊤ := by
  have h := PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp hcover
  simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using h

include hcover frame

/-- Finite presentation descends along the localization maps of sections. -/
theorem sheafGlobal_finitePresentation_of_principal_frames :
    Module.FinitePresentation R (sheafGlobalModule M) := by
  apply Module.FinitePresentation.of_localizationSpan' s (principalFrame_span_top s hcover)
    (Rₚ := fun g : s => PrincipalRing (g : R))
    (fun g : s => sheafToPrincipal M (g : R))
  intro g
  let := Module.Finite.equiv (frame g).symm
  let := Module.Projective.of_equiv (frame g).symm
  exact Module.finitePresentation_of_projective _ _

/-- Flatness descends along the same restriction maps. -/
theorem sheafGlobal_flat_of_principal_frames :
    Module.Flat R (sheafGlobalModule M) := by
  apply Module.flat_of_isLocalized_span (R := R) R (sheafGlobalModule M) s
    (principalFrame_span_top s hcover)
    (fun g : s => Γ(M, PrimeSpectrum.basicOpen (g : R)))
    (fun g : s => sheafToPrincipal M (g : R))
  intro g
  let := IsLocalization.flat (PrincipalRing (g : R)) (Submonoid.powers (g : R))
  let := Module.Projective.of_equiv (frame g).symm
  exact Module.Flat.trans R (PrincipalRing (g : R)) _

/-- The affine section module of this locally framed sheaf is projective. -/
theorem sheafGlobal_projective_of_principal_frames :
    Module.Projective R (sheafGlobalModule M) := by
  let := sheafGlobal_finitePresentation_of_principal_frames M s hcover frame
  let := sheafGlobal_flat_of_principal_frames M s hcover frame
  exact Module.Flat.projective_of_finitePresentation

/-- Finite generation is derived as part of finite-presentation descent. -/
theorem sheafGlobal_finite_of_principal_frames :
    Module.Finite R (sheafGlobalModule M) := by
  let := sheafGlobal_finitePresentation_of_principal_frames M s hcover frame
  infer_instance

/-- Every stalk rank is one, computed through a localized section module. -/
theorem sheafGlobal_rank_one_of_principal_frames (p : PrimeSpectrum R) :
    Module.rankAtStalk (sheafGlobalModule M) p = 1 := by
  have hp : p ∈ ⨆ g : s, PrimeSpectrum.basicOpen (g : R) := by rw [hcover]; trivial
  obtain ⟨g, hg⟩ := Opens.mem_iSup.mp hp
  obtain ⟨p', hp'⟩ :
      p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (PrincipalRing (g : R)))) := by
    rw [PrimeSpectrum.localization_away_comap_range (PrincipalRing (g : R)) (g : R)]
    exact hg
  let := sheafGlobal_finite_of_principal_frames M s hcover frame
  let := sheafGlobal_projective_of_principal_frames M s hcover frame
  let : Nontrivial (PrincipalRing (g : R)) := p'.nontrivial
  rw [← hp', ← Module.rankAtStalk_isBaseChange
    (IsLocalizedModule.isBaseChange (Submonoid.powers (g : R)) (PrincipalRing (g : R))
      (sheafToPrincipal M (g : R))) p', Module.rankAtStalk_eq_of_equiv (frame g),
    Module.rankAtStalk_self]
  rfl

end FlagVarieties.Foundations.QuotientPair
